import CIL.Safety.InstructionMemory

namespace CIL.Safety

theorem numberBytes_succ (value width : Nat) :
    numberBytes value (width + 1) = BitVec.ofNat 8 value :: numberBytes (value / 256) width := by
  simp only [numberBytes, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.pow_zero, Nat.div_one]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm 256]

theorem byteNumber_numberBytes (value width : Nat) :
    byteNumber (numberBytes value width) = value % 256^width := by
  induction width generalizing value with
  | zero => simp [numberBytes, byteNumber, Nat.mod_one]
  | succ width ih =>
    rw [numberBytes_succ]
    change (BitVec.ofNat 8 value).toNat + 256 * byteNumber (numberBytes (value / 256) width) = _
    rw [ih]
    simp only [BitVec.toNat_ofNat, Nat.pow_succ]
    change value % 256 + 256 * (value / 256 % 256^width) = value % (256^width * 256)
    simpa only [Nat.mod_mul_left_mod, Nat.mod_mul_left_div_self] using
      Nat.mod_add_div (value % (256^width * 256)) 256

#print axioms numberBytes_succ
#print axioms byteNumber_numberBytes

end CIL.Safety
