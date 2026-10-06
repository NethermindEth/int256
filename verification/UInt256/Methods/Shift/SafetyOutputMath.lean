import UInt256.Methods.Shift.SafetyOutput
import UInt256.Methods.Shift.ValueOutputs
import UInt256.Methods.Shift.Count

namespace UInt256Proof.Shift.Safety

/-- The values computed for the actual store call implement the independent
    256-bit left-shift operation, including cross-limb carry bits. -/
theorem shift_output_value (direction : Direction) (whole : Fin 4) (words : Fin 4 → BitVec 64) (count : BitVec 32) :
    let output := outputWords direction whole words (count &&& 63) (63 - (count &&& 63))
    pack (output.getD 0 0) (output.getD 1 0) (output.getD 2 0) (output.getD 3 0) =
      shiftValue direction (UInt256Model.value words) (64 * whole.val + count.toNat % 64) := by
  have masked : ((count &&& (63 : BitVec 32)) &&& 63).toNat % 64 = count.toNat % 64 := by
    rw [mask_count, mask_count]
    simp
  have complement : (((63 : BitVec 32) - (count &&& 63)) &&& 63).toNat % 64 =
      63 - count.toNat % 64 := by
    rw [mask_count, carry_count]
    have bound := Nat.mod_lt count.toNat (show 0 < 64 by decide)
    omega
  have bound := Nat.mod_lt count.toNat (show 0 < 64 by decide)
  have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
  cases direction <;> rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [outputWords, shiftValue, masked, complement, List.getD_cons_zero, List.getD_cons_succ,
      Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.mul_zero, Nat.zero_add,
      Nat.mul_one, Nat.reduceMul]
  · exact left_pack_zero words _ bound
  · exact left_pack_one words _ bound
  · exact left_pack_two words _ bound
  · exact left_pack_three words _ bound

  · exact right_pack_zero words _ bound
  · exact right_pack_one words _ bound
  · exact right_pack_two words _ bound
  · exact right_pack_three words _ bound

#print axioms shift_output_value
end UInt256Proof.Shift.Safety
