import CIL.Safety.Frames
import CIL.Safety.StaticMemory

namespace CIL.Safety

def numericValue : CIL.Value → Bool
  | .i8 _ | .i32 _ | .i64 _ | .v128 _ | .v256 _ => true
  | _ => false

def checkedValue (m : Memory) : Value → ExecutionResult Value
  | .reference r => formValue m r
  | .span r length => do
    let _ ← formValue m r
    return .span r length
  | .scalar value => if numericValue value then .ok (.scalar value) else .error .invalidState

/-- Only the value-only instruction whitelist may use the original pure
    arithmetic semantics. No memory/reference operation can enter this path. -/
def pureArity : CIL.Op → Option Nat
  | .convI8 | .convI4 | .convU1 | .convU4 | .convU8 | .convU | .bnot => some 1
  | .add | .sub | .mul | .band | .bor | .bxor | .shl | .shr | .shrUn
    | .lt | .ltu | .gtu | .eq => some 2
  | .brzero _ | .brnonzero _ => some 1
  | .bltu _ | .bgeu _ | .bgtu _ | .bge _ | .blt _ | .beq _ | .bne _ => some 2
  | .branch _ | .feature _ => some 0
  | .intrinsic _ argc => some argc
  | _ => none

def scalars : List Value → ExecutionResult (List CIL.Value)
  | [] => .ok []
  | .scalar value :: rest => do
    if numericValue value then return value :: (← scalars rest) else .error .invalidState
  | _ => .error .invalidState

inductive FrameAction where
  | next (pc : Nat) (stack : List Value) (frame : Frame) (memory : Memory)
  | call (callee : Nat) (args rest : List Value) (memory : Memory)
  | construct (callee : Nat) (args rest : List Value) (frame : Frame)
      (temporary : Reference) (memory : Memory)
  | returned (result : List Value) (memory : Memory)

def step (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) : ExecutionResult FrameAction := do
  match op, stack with
  | .arg i, _ =>
    let some value := args[i]? | .error .invalidState
    return .next (pc + 1) ((← checkedValue m value) :: stack) frame m
  | .aggregateArg i, _ =>
    let home ← argumentHome frame i
    return .next (pc + 1) ((← loadLocal m home) :: stack) frame m
  | .aggregateArgAddr i, _ =>
    let home ← argumentHome frame i
    return .next (pc + 1) ((← localAddress m home) :: stack) frame m
  | .local i, _ | .aggregateLocal i, _ =>
    let some slot := frame.locals[i]? | .error .invalidState
    return .next (pc + 1) ((← loadLocal m slot) :: stack) frame m
  | .localAddr i, _ | .aggregateLocalAddr i, _ =>
    let some slot := frame.locals[i]? | .error .invalidState
    return .next (pc + 1) ((← localAddress m slot) :: stack) frame m
  | .setLocal i, value :: rest | .setAggregateLocal i, value :: rest =>
    let some slot := frame.locals[i]? | .error .invalidState
    let (slot, memory) ← storeLocal m slot value
    return .next (pc + 1) rest { frame with locals := frame.locals.set i slot } memory
  | .call callee argc, _ =>
    if stack.length < argc then .error .invalidState else
      let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
      return .call callee arguments (stack.drop argc) m
  | .newValue callee argc, _ =>
    if stack.length < argc then .error .invalidState else
      let arguments ← (stack.take argc).reverse.mapM (checkedValue m)
      let (temporary, memory) ← allocateHome m frame.activation (localWidth .vector256)
      let memory ← storeValue memory (.address temporary) (.v256 0)
      let frame := { frame with owned := temporary.allocation :: frame.owned }
      return .construct callee (.reference (.address temporary) :: arguments)
        (stack.drop argc) frame temporary memory
  | .memory operation, _ =>
    let (memory, values) ← staticInstruction body pc operation stack m
    return .next (pc + 1) values frame memory
  | .ret, _ =>
    if stack.length = (if body.returnsValue then 1 else 0) then
      return .returned (← stack.mapM (checkedValue m)) m
    else .error .invalidState
  | _, _ =>
    match pureArity op with
    | some argc =>
      if stack.length < argc then .error .invalidState else
        let values ← scalars (stack.take argc)
        let some (.next target result _) :=
          CIL.step op false pc [] 0 values (fun _ => none) body.profile | .error .invalidState
        let result ← (result.map Value.scalar).mapM (checkedValue m)
        return .next target (result ++ stack.drop argc) frame m
    | none =>
      let (memory, values) ← instruction op stack m
      return .next (pc + 1) values frame memory

/-- Every executed instruction goes through the checked dispatcher. Fuel has
    the same recursive call structure as the original interpreter. Constructor
    storage belongs to its caller, so expiration of the constructor's private
    frame does not destroy the value being constructed. Static instructions use
    extraction-bound field identities and readonly allocation storage. -/
def run (program : CIL.Program) : Nat → Nat → Nat → List Value → Frame →
    List Value → Memory → Except LocatedFault (Memory × List Value)
  | 0, method, pc, _, _, _, _ => .error ⟨method, pc, .fuelExhausted⟩
  | fuel + 1, method, pc, args, frame, stack, memory => do
    let some body := program[method]? | .error ⟨method, pc, .invalidState⟩
    let some op := body.code[pc]? | .error ⟨method, pc, .invalidState⟩
    let action ← (step body op pc args frame stack memory).mapError fun fault => ⟨method, pc, fault⟩
    match action with
    | .next target stack frame memory => run program fuel method target args frame stack memory
    | .call callee arguments rest memory =>
      let some child := program[callee]? | .error ⟨method, pc, .invalidState⟩
      let (childFrame, memory) ← (enterFrame child arguments memory).mapError fun fault => ⟨method, pc, fault⟩
      let (memory, result) ← run program fuel callee 0 arguments childFrame [] memory
      run program fuel method (pc + 1) args frame (result ++ rest) memory
    | .construct callee arguments rest frame temporary memory =>
      let some child := program[callee]? | .error ⟨method, pc, .invalidState⟩
      let (childFrame, memory) ← (enterFrame child arguments memory).mapError fun fault => ⟨method, pc, fault⟩
      let (memory, result) ← run program fuel callee 0 arguments childFrame [] memory
      if !result.isEmpty then .error ⟨method, pc, .invalidState⟩ else
        let value ← (loadValue memory (.address temporary) (localWidth .vector256)).mapError
          fun fault => ⟨method, pc, fault⟩
        run program fuel method (pc + 1) args frame (.scalar value :: rest) memory
    | .returned result memory =>
      let memory := leaveFrame frame memory
      let result ← (result.mapM (checkedValue memory)).mapError fun fault => ⟨method, pc, fault⟩
      return (memory, result)

def invoke (program : CIL.Program) (fuel method : Nat) (args : List Value) (m : Memory) :
    Except LocatedFault (Memory × List Value) := do
  let some body := program[method]? | .error ⟨method, 0, .invalidState⟩
  let args ← (args.mapM (checkedValue m)).mapError fun fault => ⟨method, 0, fault⟩
  let (frame, memory) ← (enterFrame body args m).mapError fun fault => ⟨method, 0, fault⟩
  run program fuel method 0 args frame [] memory

end CIL.Safety
