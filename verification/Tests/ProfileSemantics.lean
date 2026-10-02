import CIL.ExecutionLemmas

open CIL

namespace UInt256Proof.ProfileChecks

theorem fixed_query (profile : FeatureProfile) (feature : Feature) (m : Memory)
    (stack args : List Value) (pc frame : Nat) :
    step (.feature feature) false pc args frame stack m profile =
      some (.next (pc + 1) (.i32 (if profile.evaluate feature then 1 else 0) :: stack) m) := rfl

example (m : Memory) :
    step (.intrinsic (.advSimd .extract64) 3) false 0 [] 0
      [.i32 1, .v128 0, .v128 0] m FeatureProfile.scalar = none := rfl

-- ISA availability is an execution condition even if extraction were bypassed.
example (m : Memory) (profile : FeatureProfile) (h : profile.avx512FVL = false) :
    step (.intrinsic (.avx512 .ternaryLogic) 4) false 0 [] 0
      [.i32 0xF0, .v256 0, .v256 0, .v256 0] m profile = none := by
  simp [step, Intrinsic.available, h]

-- Portable vector APIs have fallback semantics; no ISA guard is required.
example (m : Memory) :
    step (.intrinsic (.vector (.add64 256)) 2) false 0 [] 0
      [.v256 0, .v256 0] m FeatureProfile.scalar =
      some (.next 1 [.v256 0] m) := rfl

example : ¬ ({ (FeatureClass.avx512 false).representative with avx2 := false }).Valid := by decide
example : ¬ ({ (FeatureClass.avx2 false).representative with avx := false }).Valid := by decide
example : ¬ ({ (FeatureClass.avx2 false).representative with sse42 := false }).Valid := by decide

-- Foundation does not imply VL, and neither implies the independent BMI1 feature.
example : ({ (FeatureClass.avx2 false).representative with avx512F := true }).Valid := by decide
example : (FeatureClass.avx512 false).representative.Valid := by decide

example (p : FeatureProfile) (h : p.Valid) (available : p.avx512FVL = true) :
    (.avx2 .permute4x64 : Intrinsic).available p = true :=
  p.avx512FVL_implies_avx2 h available

example (m : Memory) :
    step (.memory (.store256)) false 0 [] 0
      [.v256 0, .ref (.static [0] 0)] m = none := rfl

example : binary .shl (.i64 1) (.i32 64) = some (.i64 1) := by decide
example : binary .shrUn (.i32 (BitVec.ofNat 32 (2^32 - 1))) (.i32 32) =
    some (.i32 (BitVec.ofNat 32 (2^32 - 1))) := by decide
example : binary .shr (.i32 (BitVec.ofNat 32 (2^32 - 1))) (.i32 1) =
    some (.i32 (BitVec.ofNat 32 (2^32 - 1))) := by decide
example : binary .shr (.i64 1) (.i64 1) = none := rfl

#print axioms fixed_query

end UInt256Proof.ProfileChecks
