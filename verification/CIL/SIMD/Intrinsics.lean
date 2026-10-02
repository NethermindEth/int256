import CIL.SIMD.Vector
import CIL.SIMD.AdvSimd
import CIL.SIMD.SSE
import CIL.SIMD.AVX2
import CIL.SIMD.AVX512
import CIL.SIMD.AVX
import CIL.SIMD.BMI1

namespace CIL

inductive VectorIntrinsic where
  | add64 (width : Nat) | sub64 (width : Nat) | ltu64 (width : Nat) | eq64 (width : Nat)
  | equalsAll (width : Nat)
  | band (width : Nat) | bor (width : Nat) | bxor (width : Nat) | bnot (width : Nat)
  | reinterpret (width : Nat) | zero (width : Nat) | ones (width : Nat)
  | create64 (width : Nat) | extract64 (width : Nat) | ashr64 (width : Nat)
  | byteToBool
  deriving DecidableEq, Repr

inductive AdvSimdIntrinsic where
  | extract64
  deriving DecidableEq, Repr
inductive SSEIntrinsic where
  | shiftLeftBytes | alignBytes
  deriving DecidableEq, Repr
inductive AVX2Intrinsic where
  | permute4x64 | blend32
  deriving DecidableEq, Repr
inductive AVX512Intrinsic where
  | alignRight64 | ternaryLogic
  deriving DecidableEq, Repr
inductive AVXIntrinsic where
  | moveMask64 | testZ64
  deriving DecidableEq, Repr
inductive BMI1Intrinsic where
  | bextr32
  deriving DecidableEq, Repr

/-- ISA families are explicit; the common family contains portable bit-pattern operations. -/
inductive Intrinsic where
  | vector (op : VectorIntrinsic)
  | advSimd (op : AdvSimdIntrinsic)
  | sse (op : SSEIntrinsic)
  | avx2 (op : AVX2Intrinsic)
  | avx512 (op : AVX512Intrinsic)
  | avx (op : AVXIntrinsic)
  | bmi1 (op : BMI1Intrinsic)
  deriving DecidableEq, Repr

private def boolValue (p : Bool) : Value := .i32 (if p then 1 else 0)

private def binaryVector (width : Nat) (f : {n : Nat} → BitVec n → BitVec n → BitVec n)
    : List Value → Option Value
  | [.v128 a, .v128 b] => if width == 128 then some (.v128 (f a b)) else none
  | [.v256 a, .v256 b] => if width == 256 then some (.v256 (f a b)) else none
  | _ => none

private def binaryLanes (width : Nat) (f : W64 → W64 → W64) : List Value → Option Value
  | [.v128 a, .v128 b] => if width == 128 then some (.v128 (Vector.zip128 f a b)) else none
  | [.v256 a, .v256 b] => if width == 256 then some (.v256 (Vector.zip256 f a b)) else none
  | _ => none

private def immediate (v : Value) : Option (BitVec 8) :=
  match v with
  | .i32 x => if x.toNat < 256 then some (x.setWidth 8) else none
  | _ => none

/-- Type, arity and immediate failures are explicit. ISA availability is checked during extraction. -/
def evalIntrinsic (op : Intrinsic) (args : List Value) : Option Value := do
  match op, args with
  | .vector (.add64 w), xs => binaryLanes w (· + ·) xs
  | .vector (.sub64 w), xs => binaryLanes w (· - ·) xs
  | .vector (.ltu64 w), xs => binaryLanes w (fun a b => Vector.mask64 (a.ult b)) xs
  | .vector (.eq64 w), xs => binaryLanes w (fun a b => Vector.mask64 (a == b)) xs
  | .vector (.band w), xs => binaryVector w (fun a b => a &&& b) xs
  | .vector (.bor w), xs => binaryVector w (fun a b => a ||| b) xs
  | .vector (.bxor w), xs => binaryVector w (fun a b => a ^^^ b) xs
  | .vector (.equalsAll 128), [.v128 a, .v128 b] => some (boolValue (a == b))
  | .vector (.equalsAll 256), [.v256 a, .v256 b] => some (boolValue (a == b))
  | .vector (.bnot 128), [.v128 a] => some (.v128 (~~~a))
  | .vector (.bnot 256), [.v256 a] => some (.v256 (~~~a))
  | .vector (.reinterpret 128), [.v128 a] => some (.v128 a)
  | .vector (.reinterpret 256), [.v256 a] => some (.v256 a)
  | .vector (.zero 128), [] => some (.v128 0)
  | .vector (.zero 256), [] => some (.v256 0)
  | .vector (.ones 128), [] => some (.v128 (~~~0))
  | .vector (.ones 256), [] => some (.v256 (~~~0))
  | .vector (.create64 128), [.i64 a, .i64 b] => some (.v128 (Vector.pack128 a b))
  | .vector (.create64 256), [.i64 a, .i64 b, .i64 c, .i64 d] => some (.v256 (Vector.pack256 a b c d))
  | .vector (.create64 128), [.i64 a] => some (.v128 (Vector.pack128 a a))
  | .vector (.create64 256), [.i64 a] => some (.v256 (Vector.pack256 a a a a))
  | .vector (.extract64 128), [.v128 a, .i32 i] =>
    if i.toNat < 2 then some (.i64 (Vector.lane64 a i.toNat)) else none
  | .vector (.extract64 256), [.v256 a, .i32 i] =>
    if i.toNat < 4 then some (.i64 (Vector.lane64 a i.toNat)) else none
  | .vector (.ashr64 128), [.v128 a, .i32 i] =>
    some (.v128 (Vector.map128 (fun x => x.sshiftRight (i.toNat % 64)) a))
  | .vector (.ashr64 256), [.v256 a, .i32 i] =>
    some (.v256 (Vector.map256 (fun x => x.sshiftRight (i.toNat % 64)) a))
  | .advSimd .extract64, [.v128 a, .v128 b, i] =>
    let c ← immediate i
    if c.toNat < 2 then some (.v128 (Vector.advExtract64 a b c.toNat)) else none
  | .sse .shiftLeftBytes, [.v128 a, i] =>
    let c ← immediate i
    some (.v128 (Vector.sseShiftLeftBytes a c.toNat))
  | .sse .alignBytes, [.v128 a, .v128 b, i] =>
    let c ← immediate i
    some (.v128 (Vector.ssseAlignBytes a b c.toNat))
  | .avx2 .permute4x64, [.v256 a, i] =>
    let c ← immediate i
    some (.v256 (Vector.permute4x64 a c))
  | .avx2 .blend32, [.v256 a, .v256 b, i] =>
    let c ← immediate i
    some (.v256 (Vector.blend32 a b c))
  | .avx512 .alignRight64, [.v256 a, .v256 b, i] =>
    let c ← immediate i
    some (.v256 (Vector.alignRight64 a b c.toNat))
  | .avx512 .ternaryLogic, [.v256 a, .v256 b, .v256 c, i] =>
    let control ← immediate i
    some (.v256 (Vector.ternaryLogic a b c control))
  | .avx .moveMask64, [.v256 a] => some (.i32 (Vector.moveMask64 a))
  | .avx .testZ64, [.v256 a, .v256 b] => some (boolValue ((a &&& b) == 0))
  | .bmi1 .bextr32, [.i32 a, start, length] =>
    let s ← immediate start
    let l ← immediate length
    some (.i32 (Vector.bextr32 a s.toNat l.toNat))
  | .vector .byteToBool, [.i32 a] =>
    if a.toNat < 256 then some (.i32 a) else none
  | .vector .byteToBool, [.i8 a] => some (.i32 (a.setWidth 32))
  | _, _ => none

end CIL
