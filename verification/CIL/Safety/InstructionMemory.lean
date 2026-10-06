import CIL.Safety.MemoryLemmas
import CIL.Semantics

namespace CIL.Safety

/-- References are not encoded as ordinary integers or untracked CIL addresses. -/
inductive Value where
  | scalar (value : CIL.Value)
  | reference (value : ManagedReference)
  | span (reference : ManagedReference) (length : Nat)
  deriving DecidableEq, Repr

inductive ExecutionFault where
  | memory (rule : Fault) (reference : ManagedReference) (width : Nat)
  | invalidState
  | unsupported (description : String)
  | fuelExhausted
  deriving DecidableEq, Repr

abbrev ExecutionResult := Except ExecutionFault

def checkedAt (reference : ManagedReference) (width : Nat) (result : Checked α) : ExecutionResult α :=
  result.mapError fun rule => .memory rule reference width

def referenceAt : ManagedReference → ExecutionResult Reference
  | .null => .error (.memory .nullDereference .null 0)
  | .address r => .ok r

/-- Byte order is explicit; vector/aggregate values are snapshots. -/
def byteNumber (bytes : List (BitVec 8)) : Nat :=
  bytes.foldr (fun byte high => byte.toNat + 256 * high) 0

def numberBytes (value width : Nat) : List (BitVec 8) :=
  (List.range width).map fun i => BitVec.ofNat 8 (value / 256^i)

/-- Ordinary reference-free accesses in the target CoreCLR x64/ARM64 normal-memory
    convention permit byte offsets. This is not the portable CLI natural-alignment
    rule. ALIGNMENT.md records the runtime correspondence boundary; aligned APIs,
    volatile/atomic operations and device memory are not admitted by this rule. -/
abbrev ordinaryAccessAlignment : Nat := 1

def loadValue (m : Memory) (reference : ManagedReference) (width : Nat) : ExecutionResult CIL.Value := do
  let bytes ← checkedAt reference width (dereference m reference width ordinaryAccessAlignment)
  let number := byteNumber bytes
  match width with
  | 8 => return .i64 (BitVec.ofNat 64 number)
  | 16 => return .v128 (BitVec.ofNat 128 number)
  | 32 => return .v256 (BitVec.ofNat 256 number)
  | _ => .error (.unsupported "Memory value width")

def storeValue (m : Memory) (reference : ManagedReference) (value : CIL.Value) : ExecutionResult Memory := do
  let (width, number) ← match value with
    | .i64 bits => .ok (8, bits.toNat)
    | .v128 bits => .ok (16, bits.toNat)
    | .v256 bits => .ok (32, bits.toNat)
    | _ => .error .invalidState
  let address ← referenceAt reference
  checkedAt reference width (write m address (numberBytes number width) ordinaryAccessAlignment)

def formValue (m : Memory) (reference : ManagedReference) : ExecutionResult Value := do
  match reference with
  | .null => return .reference .null
  | .address r =>
    let result ← checkedAt reference 0 (form m r)
    return .reference (.address result)

/-- This dispatch uses the actual CIL memory operation, not a source-level
    arithmetic summary. Static/span construction requires extraction-bound
    allocation metadata and is explicitly unsupported until that is supplied. -/
def memoryInstruction (operation : CIL.MemoryOp) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  match operation, stack with
  | .load128, .reference r :: rest => return (m, .scalar (← loadValue m r 16) :: rest)
  | .load256, .reference r :: rest => return (m, .scalar (← loadValue m r 32) :: rest)
  | .store128, .scalar (.v128 bits) :: .reference r :: rest =>
    return (← storeValue m r (.v128 bits), rest)
  | .store256, .scalar (.v256 bits) :: .reference r :: rest =>
    return (← storeValue m r (.v256 bits), rest)
  | .init256, .reference r :: rest => return (← storeValue m r (.v256 0), rest)
  | .asRef, .reference r :: rest => return (m, (← formValue m r) :: rest)
  | .add size signed, .scalar offset :: .reference r :: rest =>
    let some offset := CIL.offsetValue signed offset | .error .invalidState
    let address ← referenceAt r
    let result ← checkedAt r 0 (add m address size (BitVec.ofInt 64 offset))
    return (m, .reference (.address result) :: rest)
  | .bitcast256, .scalar (.v256 bits) :: rest => return (m, .scalar (.v256 bits) :: rest)
  | .bitcastByteBool, .scalar (.i32 bits) :: rest =>
    if bits.toNat ≤ 1 then return (m, .scalar (.i32 bits) :: rest)
    else .error (.unsupported "Noncanonical Boolean representation")
  | .bitcastByteBool, .scalar (.i8 bits) :: rest =>
    if bits.toNat ≤ 1 then return (m, .scalar (.i32 (bits.zeroExtend 32)) :: rest)
    else .error (.unsupported "Noncanonical Boolean representation")
  | .skipInit, .reference r :: rest =>
    let _ ← formValue m r
    return (m, rest)
  | .spanReference, .span r _ :: rest =>
    return (m, (← formValue m r) :: rest)
  | .staticAddress _, _ | .dataToken _, _ | .createSpan, _ | .spanCreate, _ =>
    .error (.unsupported "Extraction-bound static/span allocation metadata")
  | _, _ => .error .invalidState

/-- The memory part of instruction execution. Pure/control instructions and
    calls will be connected by the execution layer; they cannot fall through to
    an unchecked memory interpreter here. -/
def instruction (op : CIL.Op) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  match op, stack with
  | .memory operation, _ => memoryInstruction operation stack m
  | .const32 bits, _ => return (m, .scalar (.i32 bits) :: stack)
  | .const64 bits, _ => return (m, .scalar (.i64 bits) :: stack)
  | .load64, .reference r :: rest => return (m, .scalar (← loadValue m r 8) :: rest)
  | .store64, .scalar (.i64 bits) :: .reference r :: rest =>
    return (← storeValue m r (.i64 bits), rest)
  | .field index, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 8 (BitVec.ofNat 64 index.val))
    return (m, .scalar (← loadValue m (.address address) 8) :: rest)
  | .field index, .scalar (.v256 bits) :: rest =>
    return (m, .scalar (.i64 (CIL.Vector.lane64 bits index.val)) :: rest)
  | .fieldAddr index, .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 8 (BitVec.ofNat 64 index.val))
    return (m, .reference (.address address) :: rest)
  | .setField index, .scalar (.i64 bits) :: .reference (.address r) :: rest =>
    let address ← checkedAt (.address r) 0 (add m r 8 (BitVec.ofNat 64 index.val))
    return (← storeValue m (.address address) (.i64 bits), rest)
  | .skipInit, .reference r :: rest =>
    let _ ← formValue m r
    return (m, rest)
  | .asRef, .reference r :: rest => return (m, (← formValue m r) :: rest)
  | .dup, value :: rest => return (m, value :: value :: rest)
  | .pop, _ :: rest => return (m, rest)
  | _, _ => .error (.unsupported "Non-memory instruction requires execution adapter")

/-- Sequential semantic examples stop at the first fault. This is not the
    branch/call interpreter used to issue production certificates. -/
def instructions (ops : List CIL.Op) (stack : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) := do
  match ops with
  | [] => return (m, stack)
  | op :: rest =>
    let (memory, values) ← instruction op stack m
    instructions rest values memory

structure LocatedFault where
  method : Nat
  instruction : Nat
  fault : ExecutionFault
  deriving DecidableEq, Repr

def instructionAt (method pc : Nat) (op : CIL.Op) (stack : List Value) (m : Memory) :
    Except LocatedFault (Memory × List Value) :=
  (instruction op stack m).mapError fun fault => ⟨method, pc, fault⟩

/-- Actual straight-line CIL bodies, including argument loads and return
    shape. Branch/call/frame support remains an explicit next integration step. -/
def block (returns : Bool) (args : List Value) (ops : List CIL.Op)
    (stack : List Value) (m : Memory) : ExecutionResult (Memory × List Value) := do
  match ops with
  | [] => .error .invalidState
  | .arg index :: rest =>
    let some value := args[index]? | .error .invalidState
    let value ← match value with
      | .reference reference => formValue m reference
      | .scalar value => if value.initialized then .ok (.scalar value) else .error .invalidState
      | .span reference length => .ok (.span reference length)
    block returns args rest (value :: stack) m
  | .ret :: _ =>
    if stack.length = (if returns then 1 else 0) then return (m, stack)
    else .error .invalidState
  | op :: rest =>
    let (memory, values) ← instruction op stack m
    block returns args rest values memory

def methodBlock (body : CIL.Method) (args : List Value) (m : Memory) :
    ExecutionResult (Memory × List Value) :=
  block body.returnsValue args body.code [] m

end CIL.Safety
