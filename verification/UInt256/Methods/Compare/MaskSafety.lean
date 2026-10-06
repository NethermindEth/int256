import Extracted
import CIL.Safety.Execution
import UInt256.Methods.Compare.MaskLemmas

namespace UInt256Proof.Compare.Safety
open CIL.Safety

def maskIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any (fun op => match op with | .shl => true | _ => false) &&
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false)

def maskResult (equal less : BitVec 32) : BitVec 32 :=
  if 15 < (equal + (less <<< 1)).toNat then 1 else 0

/-- Execute the discovered numeric helper; no helper arithmetic is assumed. -/
theorem mask_invoke (memory : Memory) (equal less : BitVec 32) :
    invoke Extracted.program 8 maskIndex [.scalar (.i32 equal), .scalar (.i32 less)] memory =
      .ok (memory, [.scalar (.i32 (maskResult equal less))]) := by
  conv in maskIndex => cbv
  simp [invoke, run, cil_code, enterFrame, makeLocals, makeArgumentHomes, leaveFrame,
    step, instruction, checkedValue, numericValue, pureArity, scalars,
    CIL.step, CIL.binary, maskResult, BitVec.lt_def,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]


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
