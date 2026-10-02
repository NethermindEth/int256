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
