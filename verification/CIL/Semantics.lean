import CIL.Memory
import CIL.Instructions
import CIL.AggregateMemory

namespace CIL

def initLocals (m : Memory) (frame : Nat) (values : List Value) : Memory :=
  (values.zipIdx).foldl (fun s (v, i) => write s (.local frame i) v) m

-- Kind 0 holds struct locals; kind 1 holds by-value struct arguments; kind 2
-- holds newobj constructor temporaries. Every byte is disjoint from caller bytes.
def initFrame (m : Memory) (frame : Nat) (body : Method) (args : List Value) : Memory :=
  let locals := body.aggregateLocals.foldl (fun memory index =>
    let cleared := clearHome memory frame 0 index
    match body.locals[index]? with
    | some (.v256 bits) => writeAggregate cleared frame 0 index bits
    | _ => cleared) (initLocals m frame body.locals)
  body.aggregateArgs.foldl (fun memory index =>
    let cleared := clearHome memory frame 1 index
    match args[index]? with
    | some (.v256 bits) => writeAggregate cleared frame 1 index bits
    | _ => cleared) locals

@[simp] theorem initFrame_plain (m : Memory) (frame : Nat) (body : Method) (args : List Value)
    (hl : body.aggregateLocals = []) (ha : body.aggregateArgs = []) :
    initFrame m frame body args = initLocals m frame body.locals := by
  simp [initFrame, hl, ha]

@[simp] theorem initFrame_profile (m : Memory) (frame : Nat) (body : Method)
    (args : List Value) (profile : FeatureProfile) :
    initFrame m frame { body with profile := profile } args = initFrame m frame body args := rfl

def truth : Value → Option Bool
  | .i32 w => some (w != 0)
  | .i64 w => some (w != 0)
  | _ => none

def binary (op : Op) (a b : Value) : Option Value :=
  match op, a, b with
  | .add, .i64 x, .i64 y => some (.i64 (x + y))
  | .add, .i32 x, .i32 y => some (.i32 (x + y))
  | .sub, .i64 x, .i64 y => some (.i64 (x - y))
  | .sub, .i32 x, .i32 y => some (.i32 (x - y))
  | .mul, .i64 x, .i64 y => some (.i64 (x * y))
  | .mul, .i32 x, .i32 y => some (.i32 (x * y))
  | .band, .i64 x, .i64 y => some (.i64 (x &&& y))
  | .band, .i32 x, .i32 y => some (.i32 (x &&& y))
  | .bor, .i64 x, .i64 y => some (.i64 (x ||| y))
  | .bor, .i32 x, .i32 y => some (.i32 (x ||| y))
  | .bxor, .i64 x, .i64 y => some (.i64 (x ^^^ y))
  | .bxor, .i32 x, .i32 y => some (.i32 (x ^^^ y))
  | .shl, .i64 x, .i32 count => some (.i64 (x <<< (count.toNat % 64)))
  | .shl, .i32 x, .i32 count => some (.i32 (x <<< (count.toNat % 32)))
  | .shrUn, .i64 x, .i32 count => some (.i64 (x >>> (count.toNat % 64)))
  | .shrUn, .i32 x, .i32 count => some (.i32 (x >>> (count.toNat % 32)))
  | .shr, .i64 x, .i32 count => some (.i64 (x.sshiftRight (count.toNat % 64)))
  | .shr, .i32 x, .i32 count => some (.i32 (x.sshiftRight (count.toNat % 32)))
  | .lt, .i64 x, .i64 y => some (.i32 (if x.toInt < y.toInt then 1 else 0))
  | .lt, .i32 x, .i32 y => some (.i32 (if x.toInt < y.toInt then 1 else 0))
  | .ltu, .i64 x, .i64 y => some (.i32 (if x < y then 1 else 0))
  | .gtu, .i64 x, .i64 y => some (.i32 (if x > y then 1 else 0))
  | .ltu, .i32 x, .i32 y => some (.i32 (if x < y then 1 else 0))
  | .gtu, .i32 x, .i32 y => some (.i32 (if x > y then 1 else 0))
  | .eq, .i64 x, .i64 y => some (.i32 (if x = y then 1 else 0))
  | .eq, .i32 x, .i32 y => some (.i32 (if x = y then 1 else 0))
  | _ , _, _ => none

inductive Action where
  | next (pc : Nat) (stack : List Value) (memory : Memory)
  | call (callee : Nat) (args rest : List Value) (memory : Memory)
  | construct (callee : Nat) (args rest : List Value) (memory : Memory)
  | returned (result : List Value) (memory : Memory)

def step (op : Op) (returns : Bool) (pc : Nat) (args : List Value) (frame : Nat)
    (stack : List Value) (memory : Memory)
    (profile : FeatureProfile := FeatureProfile.scalar) : Option Action := do
  match op, stack with
  | .arg i, _ =>
    let value ← args[i]?
    if !value.initialized then none else return .next (pc + 1) (value :: stack) memory
  | .aggregateArg i, _ => return .next (pc + 1) ((← readAggregate memory frame 1 i) :: stack) memory
  | .aggregateArgAddr i, _ => return .next (pc + 1) (.ref (.home frame 1 i 0) :: stack) memory
  | .aggregateLocal i, _ => return .next (pc + 1) ((← readAggregate memory frame 0 i) :: stack) memory
  | .aggregateLocalAddr i, _ => return .next (pc + 1) (.ref (.home frame 0 i 0) :: stack) memory
  | .setAggregateLocal i, .v256 bits :: rest =>
    return .next (pc + 1) rest (writeAggregate memory frame 0 i bits)
  | .local i, _ =>
    let value ← memory (.local frame i)
    if !value.initialized then none else return .next (pc + 1) (value :: stack) memory
  | .localAddr i, _ => return .next (pc + 1) (.ref (.local frame i) :: stack) memory
  | .setLocal i, v :: rest => return .next (pc + 1) rest (write memory (.local frame i) v)
  | .field i, .object id :: rest => return .next (pc + 1) ((← read64 memory (.byte (id + 8 * i.val))) :: rest) memory
  | .fieldAddr i, .object id :: rest => return .next (pc + 1) (.ref (.byte (id + 8 * i.val)) :: rest) memory
  | .field i, .ref address :: rest =>
    return .next (pc + 1) ((← read64 memory (← unsafeAdd 8 i.val address)) :: rest) memory
  | .fieldAddr i, .ref address :: rest =>
    return .next (pc + 1) (.ref (← unsafeAdd 8 i.val address) :: rest) memory
  | .field i, .v256 bits :: rest =>
    return .next (pc + 1) (.i64 (Vector.lane64 bits i.val) :: rest) memory
  | .setField i, .i64 word :: .object base :: rest =>
    return .next (pc + 1) rest (← write64 memory (.byte (base + 8 * i.val)) word)
  | .setField i, .i64 word :: .ref address :: rest =>
    return .next (pc + 1) rest (← write64 memory (← unsafeAdd 8 i.val address) word)
  | .const64 w, _ => return .next (pc + 1) (.i64 w :: stack) memory
  | .bnot, .i64 w :: rest => return .next (pc + 1) (.i64 (~~~w) :: rest) memory
  | .bnot, .i32 w :: rest => return .next (pc + 1) (.i32 (~~~w) :: rest) memory
  | .convU4, .i64 w :: rest => return .next (pc + 1) (.i32 (w.setWidth 32) :: rest) memory
  | .convU4, .i32 w :: rest => return .next (pc + 1) (.i32 w :: rest) memory
  | .convU8, .i32 w :: rest => return .next (pc + 1) (.i64 (w.zeroExtend 64) :: rest) memory
  | .convU8, .i64 w :: rest => return .next (pc + 1) (.i64 w :: rest) memory
  | .const32 w, _ => return .next (pc + 1) (.i32 w :: stack) memory
  | .convI8, .i32 w :: rest => return .next (pc + 1) (.i64 (w.signExtend 64) :: rest) memory
  | .convI4, .i64 w :: rest => return .next (pc + 1) (.i32 (w.setWidth 32) :: rest) memory
  | .convI4, .i32 w :: rest => return .next (pc + 1) (.i32 w :: rest) memory
  | .convU1, .i32 w :: rest => return .next (pc + 1) (.i32 ((w.setWidth 8).zeroExtend 32) :: rest) memory
  | .convU1, .i64 w :: rest => return .next (pc + 1) (.i32 ((w.setWidth 8).zeroExtend 32) :: rest) memory
  | .convU, .i32 w :: rest => return .next (pc + 1) (.i64 (w.zeroExtend 64) :: rest) memory
  | .convU, .i64 w :: rest => return .next (pc + 1) (.i64 w :: rest) memory
  | .add, b :: a :: rest | .sub, b :: a :: rest
  | .band, b :: a :: rest | .bor, b :: a :: rest
  | .mul, b :: a :: rest | .bxor, b :: a :: rest
  | .shl, b :: a :: rest | .shr, b :: a :: rest | .shrUn, b :: a :: rest
  | .lt, b :: a :: rest | .ltu, b :: a :: rest | .gtu, b :: a :: rest | .eq, b :: a :: rest =>
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
  | .bltu target, .i32 b :: .i32 a :: rest => return .next (if a < b then target else pc + 1) rest memory
  | .bgeu target, .i32 b :: .i32 a :: rest => return .next (if ¬a < b then target else pc + 1) rest memory
  | .bgtu target, .i32 b :: .i32 a :: rest => return .next (if b < a then target else pc + 1) rest memory
  | .bge target, .i32 b :: .i32 a :: rest => return .next (if b.toInt ≤ a.toInt then target else pc + 1) rest memory
  | .blt target, .i32 b :: .i32 a :: rest => return .next (if a.toInt < b.toInt then target else pc + 1) rest memory
  | .beq target, .i32 b :: .i32 a :: rest => return .next (if a = b then target else pc + 1) rest memory
  | .bne target, .i32 b :: .i32 a :: rest => return .next (if a ≠ b then target else pc + 1) rest memory
  | .bgtu target, .i64 b :: .i64 a :: rest => return .next (if b < a then target else pc + 1) rest memory
  | .bge target, .i64 b :: .i64 a :: rest => return .next (if b.toInt ≤ a.toInt then target else pc + 1) rest memory
  | .blt target, .i64 b :: .i64 a :: rest => return .next (if a.toInt < b.toInt then target else pc + 1) rest memory
  | .beq target, .i64 b :: .i64 a :: rest => return .next (if a = b then target else pc + 1) rest memory
  | .bne target, .i64 b :: .i64 a :: rest => return .next (if a ≠ b then target else pc + 1) rest memory
  | .call callee argc, _ =>
    if stack.length < argc || (stack.take argc).any (! ·.initialized) then none else
      return .call callee (stack.take argc).reverse (stack.drop argc) memory
  | .newValue callee argc, _ =>
    if stack.length < argc || (stack.take argc).any (! ·.initialized) then none else
      return .construct callee
        (.ref (.home frame 2 pc 0) :: (stack.take argc).reverse) (stack.drop argc)
        (writeAggregate memory frame 2 pc 0)
  | .feature id, _ =>
    return .next (pc + 1) (.i32 (if profile.evaluate id then 1 else 0) :: stack) memory
  | .intrinsic operation argc, _ =>
    if stack.length < argc || !operation.available profile then none else
      return .next (pc + 1)
        ((← evalIntrinsic operation (stack.take argc).reverse) :: stack.drop argc) memory
  | .memory operation, _ =>
    let (updated, values) ← evalMemory operation stack memory
    return .next (pc + 1) values updated
  | .skipInit, .object _ :: rest => return .next (pc + 1) rest memory
  | .skipInit, .ref _ :: rest => return .next (pc + 1) rest memory
  | .asRef, .ref a :: rest => return .next (pc + 1) (.ref a :: rest) memory
  | .ret, _ =>
    if returns then
      match stack with
      | [v] => if v.initialized then return .returned [v] memory else none
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
    match ← step op body.returnsValue pc args frame stack memory body.profile with
    | .next target stack' memory' => run program fuel method target args frame stack' memory'
    | .call callee args' rest memory' =>
      let child ← program[callee]?
      let (final, result) ← run program fuel callee 0 args' (frame + 1) []
        (initFrame memory' (frame + 1) child args')
      run program fuel method (pc + 1) args frame (result ++ rest) final
    | .construct callee args' rest memory' =>
      let child ← program[callee]?
      let (final, result) ← run program fuel callee 0 args' (frame + 1) []
        (initFrame memory' (frame + 1) child args')
      if !result.isEmpty then none else
        run program fuel method (pc + 1) args frame
          ((← readAggregate final frame 2 pc) :: rest) final
    | .returned result final => some (final, result)

def invoke (program : Program) (fuel method : Nat) (args : List Value) (m : Memory) := do
  let body ← program[method]?
  run program fuel method 0 args 0 [] (initFrame m 0 body args)
example : binary .ltu (.i64 (BitVec.ofNat 64 (2^64-1))) (.i64 0) =
    some (.i32 0) := by decide
example : binary .add (.i64 (BitVec.ofNat 64 (2^64-1))) (.i64 1) =
    some (.i64 0) := by decide
example (m : Memory) (a : Address) (x y : Value) :
    write (write m a x) a y a = some y := by simp [write]

end CIL
