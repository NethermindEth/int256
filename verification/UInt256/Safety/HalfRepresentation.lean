import UInt256.Safety.HalfAccess
import UInt256.Safety.LimbAccess
import UInt256.VectorRepresentation

namespace UInt256Model.Safety
open CIL.Safety UInt256Proof

/-- Decode a half from the same caller bytes used by the scalar limb model. -/
theorem halfValue_two_words (bytes : Bytes) (base : Nat) :
    halfValue bytes base = CIL.Vector.pack128
      (BitVec.ofNat 64 (UInt256Model.byteNumber bytes base 8))
      (BitVec.ofNat 64 (UInt256Model.byteNumber bytes (base + 8) 8)) := by
  have loaded := read128_of_limbs (byteMemory bytes) base
    (BitVec.ofNat 64 (UInt256Model.byteNumber bytes base 8))
    (BitVec.ofNat 64 (UInt256Model.byteNumber bytes (base + 8) 8))
    (by simp [CIL.read64, read_initial]) (by simp [CIL.read64, read_initial])
  rw [read128_initial] at loaded
  exact CIL.Value.v128.inj (Option.some.inj loaded)

theorem input_half_low (memory : CIL.Safety.Memory) (reference : Reference) :
    inputHalf memory reference 0 = CIL.Vector.pack128
      (inputLimb memory reference 0) (inputLimb memory reference 1) := by
  simpa only [inputHalf, inputLimb, halfValue, Fin.val_zero, Fin.val_one,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero] using
    halfValue_two_words (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

theorem input_half_high (memory : CIL.Safety.Memory) (reference : Reference) :
    inputHalf memory reference 1 = CIL.Vector.pack128
      (inputLimb memory reference 2) (inputLimb memory reference 3) := by
  simpa only [inputHalf, inputLimb, halfValue, Fin.val_one, Fin.val_two,
    show (3 : Fin 4).val = 3 from rfl, Nat.mul_one, Nat.reduceMul, Nat.add_assoc,
    Nat.reduceAdd] using
    halfValue_two_words (fun offset => (memory.cells reference.allocation offset).bits) (reference.offset + 16)

theorem input_limbs_value (memory : CIL.Safety.Memory) (reference : Reference) :
    value (inputLimb memory reference) = inputValue memory reference := by
  exact input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

#print axioms halfValue_two_words
#print axioms input_half_low
#print axioms input_half_high
#print axioms input_limbs_value
end UInt256Model.Safety
