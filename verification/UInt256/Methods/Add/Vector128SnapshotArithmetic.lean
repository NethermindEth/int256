import UInt256.Methods.Add.Vector128FastArithmetic
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD

theorem vector128_snapshot_low (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 9 =
      correctedLo (inputLimb memory left) (inputLimb memory right) := by
  simp only [vector128SnapshotValue, show (9 : Fin 11).val = 9 from rfl]
  simpa only [input_half_low, input_half_high] using
    vector128_low_corrected (inputLimb memory left) (inputLimb memory right)

theorem vector128_snapshot_high (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 10 =
      correctedHi (inputLimb memory left) (inputLimb memory right) := by
  simp only [vector128SnapshotValue, show (10 : Fin 11).val = 10 from rfl]
  simpa only [input_half_low, input_half_high] using
    vector128_high_corrected (inputLimb memory left) (inputLimb memory right)

theorem vector128_snapshot_incoming_low (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 7 = pack128 (BitVec.ofNat 64 0)
      (carryMask (inputLimb memory left 0) (inputLimb memory right 0)) := by
  simp only [vector128SnapshotValue, show (7 : Fin 11).val = 7 from rfl]
  simp only [input_half_low, input_half_high, incoming128Low,
    halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]
  rfl

theorem vector128_snapshot_incoming_high (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 8 = pack128
      (carryMask (inputLimb memory left 1) (inputLimb memory right 1))
      (carryMask (inputLimb memory left 2) (inputLimb memory right 2)) := by
  simp only [vector128SnapshotValue, show (8 : Fin 11).val = 8 from rfl]
  simp only [input_half_low, input_half_high, incoming128High,
    halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]

theorem vector128_branch_low (memory : Memory) (left right : Reference) :
    vector128BranchValue memory left right 11 =
      propagationLo (inputLimb memory left) (inputLimb memory right) := by
  change propagating128 (vector128SnapshotValue memory left right 9)
    (vector128SnapshotValue memory left right 7) = _
  rw [vector128_snapshot_low, vector128_snapshot_incoming_low]
  exact vector128_low_propagation _ _

theorem vector128_branch_high (memory : Memory) (left right : Reference) :
    vector128BranchValue memory left right 12 =
      propagationHi (inputLimb memory left) (inputLimb memory right) := by
  change propagating128 (vector128SnapshotValue memory left right 10)
    (vector128SnapshotValue memory left right 8) = _
  rw [vector128_snapshot_high, vector128_snapshot_incoming_high]
  exact vector128_high_propagation _ _

/-- The actual saved fast condition implies the saved output halves encode
    the sum of the initial caller operands, including overlapping views. -/
theorem vector128_snapshot_fast_words (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (fast : selectedPropagation128 flag (vector128BranchValue memory left right 11)
      (vector128BranchValue memory left right 12) = BitVec.ofNat 128 0) :
    let words := sumWords (inputLimb memory left) (inputLimb memory right)
    vector128SnapshotValue memory left right 9 = pack128 (words 0) (words 1) ∧
    vector128SnapshotValue memory left right 10 = pack128 (words 2) (words 3) := by
  rw [vector128_branch_low, vector128_branch_high] at fast
  simpa only [vector128_snapshot_low, vector128_snapshot_high] using
    vector128_fast_words (inputLimb memory left) (inputLimb memory right) flag fast

#print axioms vector128_snapshot_fast_words
#print axioms vector128_snapshot_low
#print axioms vector128_snapshot_high
#print axioms vector128_snapshot_incoming_low
#print axioms vector128_snapshot_incoming_high
#print axioms vector128_branch_low
#print axioms vector128_branch_high
end UInt256Proof.Add.Safety
