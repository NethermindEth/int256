import UInt256.Methods.Add.Vector128ARMRepairChecked

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD

def vector128DecisionValues (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (i : Fin 14) : BitVec 128 :=
  if within : i.val < 13 then vector128BranchValue memory left right ⟨i.val, within⟩
  else selectedPropagation128 flag (vector128BranchValue memory left right 11) (vector128BranchValue memory left right 12)

theorem vector128_decision_values_old (memory : Memory) (left right : Reference) (flag : BitVec 32) (i : Fin 13) :
    vector128DecisionValues memory left right flag ⟨i.val, by omega⟩ = vector128BranchValue memory left right i := by
  simp only [vector128DecisionValues, dite_eq_left i.isLt]

theorem vector128_decision_repair_mask (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    repair128Mask (vector128DecisionValues memory left right flag 10)
      (vector128DecisionValues memory left right flag 11) (vector128DecisionValues memory left right flag 12) =
      extraHi (inputLimb memory left) (inputLimb memory right) := by
  change repair128Mask (vector128SnapshotValue memory left right 10)
    (vector128BranchValue memory left right 11) (vector128BranchValue memory left right 12) = _
  rw [vector128_snapshot_high, vector128_branch_low, vector128_branch_high]
  exact vector128_arm_extra_value _ _

theorem vector128_repaired_snapshot_high (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (vector128DecisionValues memory left right flag) 10 =
      repairedHi (inputLimb memory left) (inputLimb memory right) := by
  change corrected128 (vector128SnapshotValue memory left right 10)
    (repair128Mask (vector128DecisionValues memory left right flag 10)
      (vector128DecisionValues memory left right flag 11) (vector128DecisionValues memory left right flag 12)) = _
  rw [vector128_snapshot_high, vector128_decision_repair_mask]
  exact vector128_arm_repaired_high _ _

theorem vector128_repaired_snapshot_carry (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (vector128DecisionValues memory left right flag) 6 =
      UInt256Proof.Reporting.repairedCarryHi (inputLimb memory left) (inputLimb memory right) := by
  change repaired128Carry (vector128SnapshotValue memory left right 6)
    (vector128BranchValue memory left right 12) (full128 (vector128SnapshotValue memory left right 10))
    (repair128Mask (vector128DecisionValues memory left right flag 10)
      (vector128DecisionValues memory left right flag 11) (vector128DecisionValues memory left right flag 12)) = _
  rw [vector128_snapshot_high_carry, vector128_branch_high, vector128_snapshot_high, vector128_decision_repair_mask]
  exact vector128_arm_repaired_carry _ _

#print axioms vector128_decision_values_old
#print axioms vector128_decision_repair_mask
#print axioms vector128_repaired_snapshot_high
#print axioms vector128_repaired_snapshot_carry
end UInt256Proof.Add.Safety
