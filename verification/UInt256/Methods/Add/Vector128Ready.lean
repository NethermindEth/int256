import UInt256.Methods.Add.Vector128PropagationPair

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128BranchValue (memory : Memory) (left right : Reference) (i : Fin 13) : BitVec 128 :=
  if within : i.val < 11 then vector128SnapshotValue memory left right ⟨i.val, within⟩
  else if i.val = 11 then
    propagating128 (vector128SnapshotValue memory left right 9) (vector128SnapshotValue memory left right 7)
  else propagating128 (vector128SnapshotValue memory left right 10) (vector128SnapshotValue memory left right 8)

/-- Entry through the propagation decision, with all thirteen saved values
    tied to the initial inputs and early ARM output readbacks still valid. -/
theorem vector128_ready_checked (original entered : Memory)
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
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
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
        run Extracted.program fuel vector128Index 94 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_output_prefix original entered inputs outputs left right output frame slots args call setup
    layout homes leftMember rightMember outputMember leftArg rightArg outputArg post
  intro current snapshots outputRead currentCall authority footprint advanced callerPreserved
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  obtain ⟨lowIncoming, lowIncomingSlot, lowIncomingRead⟩ := snapshots 7
  obtain ⟨highIncoming, highIncomingSlot, highIncomingRead⟩ := snapshots 8
  apply vector128_propagation_pair original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    (vector128SnapshotValue original left right 9) (vector128SnapshotValue original left right 10)
    (vector128SnapshotValue original left right 7) (vector128SnapshotValue original left right 8)
    lowHome highHome lowIncoming highIncoming lowSlot highSlot lowIncomingSlot highIncomingSlot
    lowRead highRead lowIncomingRead highIncomingRead post
  intro lowMask highMask after lowMaskSlot highMaskSlot lowMaskRead highMaskRead kept preserved afterCall afterAuthority next
  have ready : ∀ i : Fin 13, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16) := by
    intro i
    by_cases within : i.val < 11
    · obtain ⟨reference, slot, loaded⟩ := snapshots ⟨i.val, within⟩
      refine ⟨reference, slot, ?_⟩
      simp only [vector128BranchValue, dif_pos within]
      exact kept i.val within reference _ slot loaded
    · have cases : i = 11 ∨ i = 12 := by omega
      rcases cases with rfl | rfl
      · exact ⟨lowMask, lowMaskSlot, lowMaskRead⟩
      · exact ⟨highMask, highMaskSlot, highMaskRead⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have retainedOutput : Extracted.profile.advSimd = true →
      read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
      read after { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16) := by
    intro enabled
    exact ⟨(preserved.read output old 16 1).trans (outputRead enabled).1,
      (preserved.read { output with offset := output.offset + 16 } old 16 1).trans (outputRead enabled).2⟩
  exact continuation after ready retainedOutput afterCall afterAuthority
    (fun id offset bound outside => (preserved.cells id bound offset).trans (footprint id offset bound outside))
    (Nat.le_trans advanced next)
    (fun disabled => (callerPreserved disabled).trans preserved)

#print axioms vector128_ready_checked
end UInt256Proof.Add.Safety
