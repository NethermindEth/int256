import UInt256.Methods.Add.Vector128ARMRepairUpdate
import UInt256.Methods.Add.Vector128SnapshotArithmetic

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD

/-- The checked ARM extraction/OR expression is the independently specified
    propagated repair mask. -/
theorem vector128_arm_extra_value (a b : Limbs) :
    incoming128High (propagationLo a b) (propagationHi a b) |||
      incoming128Low (full128 (correctedHi a b) &&&
        incoming128High (propagationLo a b) (propagationHi a b)) = extraHi a b := by
  simp only [extraHi, full128, show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl]
  rw [incoming128_arm_low]
  simp only [propagationARM, incoming128_arm_high]

theorem vector128_arm_repaired_high (a b : Limbs) :
    corrected128 (correctedHi a b) (extraHi a b) = repairedHi a b := by rfl

theorem vector128_arm_repaired_carry (a b : Limbs) :
    repaired128Carry (pack128 (carryMask (a 2) (b 2)) (carryMask (a 3) (b 3)))
      (propagationHi a b) (full128 (correctedHi a b)) (extraHi a b) =
      UInt256Proof.Reporting.repairedCarryHi a b := by
  simp only [repaired128Carry, UInt256Proof.Reporting.repairedCarryHi, full128, BitVec.or_assoc,
    show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl]

theorem vector128_snapshot_high_carry (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 6 =
      pack128 (carryMask (inputLimb memory left 2) (inputLimb memory right 2))
        (carryMask (inputLimb memory left 3) (inputLimb memory right 3)) := by
  simp only [vector128SnapshotValue, show (6 : Fin 11).val = 6 from rfl,
    input_half_high, halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]

#print axioms vector128_arm_extra_value
#print axioms vector128_arm_repaired_high
#print axioms vector128_arm_repaired_carry
#print axioms vector128_snapshot_high_carry
end UInt256Proof.Add.Safety
