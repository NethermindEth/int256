import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.ARMRepairMasks
import UInt256.Safety.VectorFrame

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector CIL.Vector

def repaired128Carry (carry propagation full repair : BitVec 128) : BitVec 128 :=
  carry ||| (propagation ||| (full &&& repair))

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD

/-- The checked ARM extraction/OR expression is the independently specified propagated repair mask. -/
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

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def repair128Mask (high lowPropagation highPropagation : BitVec 128) : BitVec 128 :=
  incoming128High lowPropagation highPropagation |||
    incoming128Low (full128 high &&& incoming128High lowPropagation highPropagation)

def armRepairSnapshot (values : Fin 14 → BitVec 128) (i : Fin 14) : BitVec 128 :=
  let repair := repair128Mask (values 10) (values 11) (values 12)
  if i.val = 6 then repaired128Carry (values 6) (values 12) (full128 (values 10)) repair
  else if i.val = 10 then corrected128 (values 10) repair else values i

/-- Complete ARM private repair state from the selected propagation condition through both
    overwrites, retaining all unaffected original snapshots. -/
theorem vector128_arm_repair_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode))
    (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : Option ManagedReference)
    (slots : List LocalSlot) (layout : frame.locals = .root root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary armSpecs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (argument : args[3]? = some (.scalar (.i32 flag)))
    (values : Fin 14 → BitVec 128)
    (condition : values 13 =
      selectedPropagation128 body.profile.advSimd flag (values 11) (values 12))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (armRepairSnapshot values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run program fuel method 149 args frame [] after = .ok (final, returned) ∧
          post final returned) :
    ∃ fuel final returned,
      run program fuel method 113 args frame [] current = .ok (final, returned) ∧
        post final returned := by
  have known := savedVectors_snapshots layout snapshots
  have formed := currentCall.1.wellFormed
  have valid := currentCall.1
  have preserved := MemoryBelow.refl boundary current
  have suffix : ∃ fuel final returned, run program fuel method 121 args frame
      [.scalar (.v128 (incoming128High (values 11) (values 12)))] current =
        .ok (final, returned) ∧ post final returned := by
    cil_contract_steps (snapshots := known) [found, code, enabled, savedVectors]
    obtain ⟨next, world⟩ :=
      (by written_from_context : WrittenFrom current storedLocal_5).kept currentCall.2
    refine continuation _ (fun i => ?_) preserved ⟨valid, world⟩ authority (Nat.le_of_eq next.symm)
    obtain ⟨home, slot, _⟩ := snapshots i
    refine ⟨home, slot, localSnapshots_5.read_vector128 (index := i.val + 1) ?_
      (by simpa [layout] using slot)⟩
    obtain ⟨index, bound⟩ := i
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨
        index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨
        index = 12 ∨ index = 13 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp [rememberLocal, savedVectors, armRepairSnapshot, repaired128Carry,
        repair128Mask, corrected128, full128, ← incoming128_arm_low]
  by_cases zero : flag = BitVec.ofNat 32 0
  · rw [← show values 13 = incoming128High (values 11) (values 12) by
      simpa [selectedPropagation128, enabled, zero] using condition] at suffix
    cil_contract_steps (snapshots := known) [found, code, argument, flagFit, zero, savedVectors]
      until suffix
  · rw [← incoming128_arm_high] at suffix
    cil_contract_steps (snapshots := known) [found, code, argument, flagFit, zero, enabled,
      savedVectors] until suffix
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD

def vector128DecisionValues (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (i : Fin 14) : BitVec 128 :=
  if within : i.val < 13 then vector128BranchValue memory left right ⟨i.val, within⟩
  else selectedPropagation128 advSimd flag (vector128BranchValue memory left right 11) (vector128BranchValue memory left right 12)

theorem vector128_decision_repair_mask (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    repair128Mask (vector128DecisionValues advSimd memory left right flag 10)
      (vector128DecisionValues advSimd memory left right flag 11) (vector128DecisionValues advSimd memory left right flag 12) =
      extraHi (inputLimb memory left) (inputLimb memory right) := by
  change repair128Mask (vector128SnapshotValue memory left right 10)
    (vector128BranchValue memory left right 11) (vector128BranchValue memory left right 12) = _
  rw [vector128_snapshot_high, vector128_branch_low, vector128_branch_high]
  exact vector128_arm_extra_value _ _

theorem vector128_repaired_snapshot_high (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (vector128DecisionValues advSimd memory left right flag) 10 =
      repairedHi (inputLimb memory left) (inputLimb memory right) := by
  change corrected128 (vector128SnapshotValue memory left right 10)
    (repair128Mask (vector128DecisionValues advSimd memory left right flag 10)
      (vector128DecisionValues advSimd memory left right flag 11) (vector128DecisionValues advSimd memory left right flag 12)) = _
  rw [vector128_snapshot_high, vector128_decision_repair_mask]
  exact vector128_arm_repaired_high _ _

theorem vector128_repaired_snapshot_carry (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (vector128DecisionValues advSimd memory left right flag) 6 =
      UInt256Proof.Reporting.repairedCarryHi (inputLimb memory left) (inputLimb memory right) := by
  change repaired128Carry (vector128SnapshotValue memory left right 6)
    (vector128BranchValue memory left right 12) (full128 (vector128SnapshotValue memory left right 10))
    (repair128Mask (vector128DecisionValues advSimd memory left right flag 10)
      (vector128DecisionValues advSimd memory left right flag 11) (vector128DecisionValues advSimd memory left right flag 12)) = _
  rw [vector128_snapshot_high_carry, vector128_branch_high, vector128_snapshot_high, vector128_decision_repair_mask]
  exact vector128_arm_repaired_carry _ _

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Reporting

/-- The actual fast-return mask encodes overflow when reporting was requested. -/
theorem vector128_snapshot_fast_flag (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (reporting : flag ≠ BitVec.ofNat 32 0)
    (fast : selectedPropagation128 advSimd flag (vector128BranchValue memory left right 11)
      (vector128BranchValue memory left right 12) = BitVec.ofNat 128 0) :
    (if lane64 (vector128SnapshotValue memory left right 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [vector128_branch_low, vector128_branch_high] at fast
  have carry := vector128_reporting_fast_carry advSimd (inputLimb memory left) (inputLimb memory right)
    flag reporting fast
  rw [vector128_snapshot_high_carry, lane128_1, carry_mask_negative, ← carry]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

/-- The repaired high mask gives overflow of the original caller operands. -/
theorem vector128_snapshot_repaired_flag (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    (if lane64 (armRepairSnapshot (vector128DecisionValues advSimd memory left right flag) 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [vector128_repaired_snapshot_carry, repaired_high_flag]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

end UInt256Proof.Add.Safety
