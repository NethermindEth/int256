import UInt256.ExecutionAutomation
import UInt256.Methods.Compare.Contract
import UInt256.Methods.Compare.VectorMasks

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Compare

macro "native_comparison_execute" initial:ident "," left:ident "," right:ident : tactic =>
  `(tactic| (
    have nativeBody : (Extracted.program.any fun method => method.code.any fun op =>
      match op with | .intrinsic (.avx512 _) _ => true | _ => false) = true := by decide
    have maskBound := orderingMask_bound (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)
    have reverseBound := orderingMask_bound (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)
    have strict := orderingMask_lt (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)
    have inclusive := orderingMask_le (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)
    have reverseStrict := orderingMask_lt (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)
    have reverseInclusive := orderingMask_le (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)
    have signedStrict := mask_sub_toInt (orderingMask (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)) 85 maskBound (by decide)
    have signedInclusive := mask_sub_toInt (orderingMask (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)) 86 maskBound (by decide)
    have signedReverseStrict := mask_sub_toInt (orderingMask (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)) 85 reverseBound (by decide)
    have signedReverseInclusive := mask_sub_toInt (orderingMask (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)) 86 reverseBound (by decide)
    have cast85 : ((85 : Nat) : Int) = (85 : Int) := rfl
    have cast86 : ((86 : Nat) : Int) = (86 : Int) := rfl
    rw [cast85] at signedStrict signedReverseStrict
    rw [cast86] at signedInclusive signedReverseInclusive
    refine ⟨executionBound Extracted.program Extracted.entryIndex,?_⟩
    simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,
      UInt256Model.Compare.holds,Int.ofNat_lt,Int.ofNat_le]
    rw [←input_value $initial:ident $left:ident,←input_value $initial:ident $right:ident]
    cil_execute_core read256_initial_limbs,evalMemory,intrinsic_native_eq,intrinsic_native_gt,intrinsic_native_lt,
      intrinsic_avx_blend,intrinsic_avx2_blend,intrinsic_native_mask,intrinsic_reinterpret256,nativeOrderingMask,nativeOrderingReverseMask,
      UInt256Model.Equality.booleanWord with fail
    all_goals try (rw [signedStrict])
    all_goals try (rw [signedInclusive])
    all_goals try (rw [signedReverseStrict])
    all_goals try (rw [signedReverseInclusive])
    all_goals clear signedStrict signedInclusive signedReverseStrict signedReverseInclusive
    all_goals refine ⟨_,⟨rfl,?_⟩,?_⟩
    all_goals try (solve | intro address; simp only [write]; rfl)
    all_goals repeat' (split <;> try simp_all (config := { implicitDefEqProofs := false }))
    all_goals omega
  ))

macro "portable_comparison_execute" initial:ident "," left:ident "," right:ident : tactic =>
  `(tactic| (
    have portableBody : (Extracted.program.any fun method => method.code.any fun op =>
      match op with | .intrinsic (.vector (.extractMSB64 256)) _ => true | _ => false) = true := by decide
    have maskBound := equalityMask_bound (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)
    have lessBound := lessMask_bound (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)
    have reverseMaskBound := equalityMask_bound (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)
    have reverseLessBound := lessMask_bound (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)
    have strict := masks_sum_lt (inputLimbs $initial:ident $left:ident) (inputLimbs $initial:ident $right:ident)
    have reverseStrict := masks_sum_lt (inputLimbs $initial:ident $right:ident) (inputLimbs $initial:ident $left:ident)
    refine ⟨executionBound Extracted.program Extracted.entryIndex,?_⟩
    simp (config := { implicitDefEqProofs := false }) only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some,
      UInt256Model.Compare.holds,Int.ofNat_lt,Int.ofNat_le]
    rw [←input_value $initial:ident $left:ident,←input_value $initial:ident $right:ident]
    cil_execute_core read256_initial_limbs,evalMemory,intrinsic_portable_eq,intrinsic_portable_lt,
      intrinsic_portable_mask,portableEqualityMask,portableLessMask,UInt256Model.Equality.booleanWord with fail
    all_goals try (simp only [BitVec.toNat_ofNat,BitVec.toNat_add,BitVec.toNat_shiftLeft,BitVec.toInt_eq_toNat_cond])
    all_goals try (refine ⟨_,⟨rfl,?_⟩,?_⟩)
    all_goals try (solve | intro address; simp only [write]; rfl)
    all_goals repeat' (split <;> try simp_all (config := { implicitDefEqProofs := false }))
    all_goals try (simp only [BitVec.lt_def,BitVec.le_def,BitVec.toNat_ofNat,
      BitVec.toNat_add,BitVec.toNat_shiftLeft] at *)
    all_goals omega
  ))

end UInt256Proof.Compare
