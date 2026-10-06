import UInt256.Methods.Add.Vector128Decision

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete checked helper prefix through the actual fast/repair branch,
    preserving all saved values and any early ARM output writes. -/
theorem vector128_dispatch_checked (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vector128Body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after conditionHome,
      slots[13]? = some (.bytes .vector128 conditionHome) →
      read after conditionHome 16 1 = .ok (numberBytes
        (selectedPropagation128 flag (vector128BranchValue original left right 11)
          (vector128BranchValue original left right 12)).toNat 16) →
      (∀ i : Fin 13, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16)) →
      (Extracted.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16)) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) →
      entered.nextIdentity ≤ after.nextIdentity →
      (Extracted.profile.advSimd = false → MemoryBelow original.nextIdentity original after) →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index
          (if selectedPropagation128 flag (vector128BranchValue original left right 11)
            (vector128BranchValue original left right 12) = BitVec.ofNat 128 0 then 204 else 111) args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_ready_checked original entered inputs outputs left right output frame slots args
    call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg post
  intro current snapshots outputRead currentCall authority footprint advanced callerPreserved
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 11
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 12
  have actualLow : (vector128SavedFrame frame slots right).locals[12]? = some (.bytes .vector128 lowHome) := by
    change slots[11]? = some (.bytes .vector128 lowHome)
    exact lowSlot
  have actualHigh : (vector128SavedFrame frame slots right).locals[13]? = some (.bytes .vector128 highHome) := by
    change slots[12]? = some (.bytes .vector128 highHome)
    exact highSlot
  apply vector128_decision_checked original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority flag flagArg
    (vector128BranchValue original left right 11) (vector128BranchValue original left right 12)
    lowHome highHome actualLow actualHigh lowRead highRead post
  intro conditionHome after conditionSlot conditionRead preserved afterCall afterAuthority written
  have conditionTail : slots[13]? = some (.bytes .vector128 conditionHome) := by
    exact conditionSlot
  have retained : ∀ i : Fin 13, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, vector128_prior_read entered current after original.nextIdentity slots homes
      i.val 13 i.isLt reference conditionHome slot conditionTail _ _ written loaded⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have retainedOutput : Extracted.profile.advSimd = true →
      read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
      read after { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16) := by
    intro enabled
    exact ⟨(preserved.read output old 16 1).trans (outputRead enabled).1,
      (preserved.read { output with offset := output.offset + 16 } old 16 1).trans (outputRead enabled).2⟩
  apply vector128_decision_branch after (vector128SavedFrame frame slots right) args conditionHome
    _ conditionSlot conditionRead post
  exact continuation after conditionHome conditionTail conditionRead retained retainedOutput afterCall afterAuthority
    (fun id offset bound outside => (preserved.cells id bound offset).trans (footprint id offset bound outside))
    (Nat.le_trans advanced (write_extends_allocations _ _ _ _ _ written).next)
    (fun disabled => (callerPreserved disabled).trans preserved)

#print axioms vector128_dispatch_checked
end UInt256Proof.Add.Safety
