import CIL.Safety.Execution
import CIL.Safety.StepComposition
import UInt256.Methods.Compare.MaskLemmas
namespace UInt256Proof.Compare.Safety
open CIL.Safety
def maskBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .arg 1,
  .const32 1,
  .shl,
  .add,
  .const32 (BitVec.ofInt 32 (15)),
  .gtu,
  .ret (some .unsigned8)] }
def maskResult (equal less : BitVec 32) : BitVec 32 :=
  if 15 < (equal + (less <<< 1)).toNat then 1 else 0

/-- Execute the discovered numeric helper; no helper arithmetic is assumed. -/
theorem mask_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat) (found : program[index]? = some (maskBody profile)) (memory : CIL.Safety.Memory) (equal less : BitVec 32) :
    CIL.Safety.invoke program 8 index [.scalar (.i32 equal), .scalar (.i32 less)] memory =
      .ok (memory, [.scalar (.i32 (maskResult equal less))]) := by
  refine invoke_of_run found rfl rfl ?_
  repeat refine (run_next found rfl rfl).trans ?_
  refine (run_return found rfl rfl rfl).trans ?_
  simp [leaveFrame, maskResult, CIL.NarrowKind.extend, BitVec.lt_def]
  split <;> rfl

theorem mask_result_math (left right : UInt256Model.Limbs) :
    maskResult (BitVec.ofNat 32 (equalityMask left right)) (BitVec.ofNat 32 (lessMask left right)) =
      if (UInt256Model.value left).toNat < (UInt256Model.value right).toNat then 1 else 0 := by
  have equalBound := equalityMask_bound left right
  have lessBound := lessMask_bound left right
  have eqSmall : equalityMask left right < 2^32 := by omega
  have ltSmall : lessMask left right < 2^32 := by omega
  have shiftedSmall : 2 * lessMask left right < 2^32 := by omega
  have sumSmall : equalityMask left right + 2 * lessMask left right < 2^32 := by omega
  simp only [maskResult, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt eqSmall, Nat.mod_eq_of_lt ltSmall]
  simp only [Nat.shiftLeft_eq, show (2 : Nat)^1 = 2 from rfl, Nat.mod_eq_of_lt shiftedSmall,
    Nat.mod_eq_of_lt sumSmall, Nat.mul_comm (lessMask left right) 2, masks_sum_lt]

#print axioms mask_result_math

#print axioms mask_invoke
end UInt256Proof.Compare.Safety
