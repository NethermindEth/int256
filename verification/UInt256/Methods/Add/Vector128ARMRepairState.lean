import UInt256.Methods.Add.Vector128ARMRepairPrepare

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def armRepairSnapshot (values : Fin 14 → BitVec 128) (i : Fin 14) : BitVec 128 :=
  let repair := repair128Mask (values 10) (values 11) (values 12)
  if i.val = 6 then repaired128Carry (values 6) (values 12) (full128 (values 10)) repair
  else if i.val = 10 then corrected128 (values 10) repair else values i

/-- Complete ARM private repair state from the selected propagation condition
    through both overwrites, retaining all unaffected original snapshots. -/
theorem vector128_arm_repair_checked (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (argument : args[3]? = some (.scalar (.i32 flag)))
    (values : Fin 14 → BitVec 128)
    (condition : values 13 = selectedPropagation128 flag (values 11) (values 12))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (armRepairSnapshot values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 149 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 113 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_arm_prepare enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority flag argument values condition snapshots post
  intro fullHome repairHome middle fullSlot repairSlot fullRead repairRead saved preserved middleCall middleAuthority advanced
  obtain ⟨carryHome, carrySlot, carryRead⟩ := saved 6
  obtain ⟨propagationHome, propagationSlot, propagationRead⟩ := saved 12
  obtain ⟨highHome, highSlot, highRead⟩ := saved 10
  change slots[6]? = _ at carrySlot
  change slots[12]? = _ at propagationSlot
  change slots[10]? = _ at highSlot
  have actualCarry : frame.locals[7]? = some (.bytes .vector128 carryHome) := by simpa [layout] using carrySlot
  have actualPropagation : frame.locals[13]? = some (.bytes .vector128 propagationHome) := by simpa [layout] using propagationSlot
  have actualFull : frame.locals[21]? = some (.bytes .vector128 fullHome) := by simpa [layout] using fullSlot
  have actualRepair : frame.locals[23]? = some (.bytes .vector128 repairHome) := by simpa [layout] using repairSlot
  apply vector128_arm_update_pair enabled boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority (values 6) carryHome actualCarry carryRead
    (values 12) propagationHome actualPropagation propagationRead (full128 (values 10)) fullHome actualFull fullRead
    (repair128Mask (values 10) (values 11) (values 12)) repairHome actualRepair repairRead
    (values 10) highHome highSlot highRead post
  intro updatedCarry updatedHigh after updatedCarrySlot updatedHighSlot updatedCarryRead updatedHighRead kept
    finalPreserved afterCall afterAuthority next
  have complete : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (armRepairSnapshot values i).toNat 16) := by
    intro i
    by_cases carry : i.val = 6
    · have same : i = 6 := by omega
      subst i
      exact ⟨updatedCarry, updatedCarrySlot, updatedCarryRead⟩
    · by_cases high : i.val = 10
      · have same : i = 10 := by omega
        subst i
        exact ⟨updatedHigh, updatedHighSlot, updatedHighRead⟩
      · obtain ⟨reference, slot, loaded⟩ := saved i
        refine ⟨reference, slot, ?_⟩
        simp only [armRepairSnapshot, carry, high, ite_false]
        exact kept i.val carry high reference _ slot loaded
  exact continuation after complete (preserved.trans finalPreserved) afterCall afterAuthority (Nat.le_trans advanced next)

#print axioms vector128_arm_repair_checked
end UInt256Proof.Add.Safety

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
