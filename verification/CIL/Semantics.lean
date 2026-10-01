import CIL.Memory
import CIL.Instructions

namespace CIL

def initLocals (m : Memory) (frame : Nat) (values : List Value) : Memory :=
  (values.zipIdx).foldl (fun s (v, i) => write s (.local frame i) v) m

def truth : Value → Option Bool
  | .i32 w => some (w != 0)
  | .i64 w => some (w != 0)
  | _ => none

def binary (op : Op) (a b : Value) : Option Value :=
  match op, a, b with
  | .add, .i64 x, .i64 y => some (.i64 (x + y))
  | .add, .i32 x, .i32 y => some (.i32 (x + y))
  | .bor, .i64 x, .i64 y => some (.i64 (x ||| y))
  | .bor, .i32 x, .i32 y => some (.i32 (x ||| y))
  | .ltu, .i64 x, .i64 y => some (.i32 (if x < y then 1 else 0))
  | .gtu, .i64 x, .i64 y => some (.i32 (if x > y then 1 else 0))
  | .eq, .i64 x, .i64 y => some (.i32 (if x = y then 1 else 0))
  | .eq, .i32 x, .i32 y => some (.i32 (if x = y then 1 else 0))
  | _ , _, _ => none

inductive Action where
  | next (pc : Nat) (stack : List Value) (memory : Memory)
  | call (callee : Nat) (args rest : List Value) (memory : Memory)
  | returned (result : List Value) (memory : Memory)

def step (op : Op) (returns : Bool) (pc : Nat) (args : List Value) (frame : Nat)
    (stack : List Value) (memory : Memory) : Option Action := do
  match op, stack with
  | .arg i, _ => return .next (pc + 1) ((← args[i]?) :: stack) memory
  | .local i, _ => return .next (pc + 1) ((← memory (.local frame i)) :: stack) memory
  | .localAddr i, _ => return .next (pc + 1) (.ref (.local frame i) :: stack) memory
  | .setLocal i, v :: rest => return .next (pc + 1) rest (write memory (.local frame i) v)
  | .field i, .object id :: rest => return .next (pc + 1) ((← read64 memory (.byte (id + 8 * i.val))) :: rest) memory
  | .fieldAddr i, .object id :: rest => return .next (pc + 1) (.ref (.byte (id + 8 * i.val)) :: rest) memory
  | .const32 w, _ => return .next (pc + 1) (.i32 w :: stack) memory
  | .convI8, .i32 w :: rest => return .next (pc + 1) (.i64 (w.signExtend 64) :: rest) memory
  | .add, b :: a :: rest | .bor, b :: a :: rest
  | .ltu, b :: a :: rest | .gtu, b :: a :: rest | .eq, b :: a :: rest =>
    return .next (pc + 1) ((← binary op a b) :: rest) memory
  | .load64, .ref a :: rest =>
    match ← read64 memory a with
    | .i64 w => return .next (pc + 1) (.i64 w :: rest) memory
    | _ => none
  | .store64, .i64 w :: .ref a :: rest => return .next (pc + 1) rest (← write64 memory a w)
  | .dup, v :: rest => return .next (pc + 1) (v :: v :: rest) memory
  | .pop, _ :: rest => return .next (pc + 1) rest memory
  | .branch target, _ => return .next target stack memory
  | .brzero target, v :: rest => return .next (if ← truth v then pc + 1 else target) rest memory
  | .brnonzero target, v :: rest => return .next (if ← truth v then target else pc + 1) rest memory
  | .bltu target, .i64 b :: .i64 a :: rest => return .next (if a < b then target else pc + 1) rest memory
  | .bgeu target, .i64 b :: .i64 a :: rest => return .next (if a < b then pc + 1 else target) rest memory
  | .call callee argc, _ =>
    if stack.length < argc then none else return .call callee (stack.take argc).reverse (stack.drop argc) memory
  | .featureDisabled, _ => return .next (pc + 1) (.i32 0 :: stack) memory
  | .skipInit, .object _ :: rest => return .next (pc + 1) rest memory
  | .asRef, .ref a :: rest => return .next (pc + 1) (.ref a :: rest) memory
  | .ret, _ =>
    if returns then
      match stack with
      | [v] => return .returned [v] memory
      | _ => none
    else if stack.isEmpty then return .returned [] memory else none
  | _, _ => none

-- Fuel is a bound on nested instruction execution. Exhaustion is failure.
def run (program : Program) : Nat → Nat → Nat → List Value → Nat → List Value → Memory →
    Option (Memory × List Value)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, method, pc, args, frame, stack, memory => do
    let body ← program[method]?
    let op ← body.code[pc]?
    match ← step op body.returnsValue pc args frame stack memory with
    | .next target stack' memory' => run program fuel method target args frame stack' memory'
    | .call callee args' rest memory' =>
      let child ← program[callee]?
      let (final, result) ← run program fuel callee 0 args' (frame + 1) []
        (initLocals memory' (frame + 1) child.locals)
      run program fuel method (pc + 1) args frame (result ++ rest) final
    | .returned result final => some (final, result)

def invoke (program : Program) (fuel method : Nat) (args : List Value) (m : Memory) := do
  let body ← program[method]?
  run program fuel method 0 args 0 [] (initLocals m 0 body.locals)
example : binary .ltu (.i64 (BitVec.ofNat 64 (2^64-1))) (.i64 0) =
    some (.i32 0) := by decide
example : binary .add (.i64 (BitVec.ofNat 64 (2^64-1))) (.i64 1) =
    some (.i64 0) := by decide
example (m : Memory) (a : Address) (x y : Value) :
    write (write m a x) a y a = some y := by simp [write]

end CIL
