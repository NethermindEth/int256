import UInt256.Methods.Add.Vector128EarlyOutput

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Execution from helper entry through the ISA-dependent early output stage.
    Saved operands remain initial-value snapshots even after overlapping writes. -/
theorem vector128_output_prefix (original entered : Memory)
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
      (∀ i : Fin 11, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16)) →
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
        run Extracted.program fuel vector128Index 82 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_snapshots_checked original entered inputs outputs left right frame slots args call setup
    layout homes leftMember rightMember leftArg rightArg post
  intro current snapshots preserved currentCall authority advanced
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  change slots[9]? = some (.bytes .vector128 lowHome) at lowSlot
  change slots[10]? = some (.bytes .vector128 highHome) at highSlot
  have actualLow : (vector128SavedFrame frame slots right).locals[10]? = some (.bytes .vector128 lowHome) := by
    simpa [vector128SavedFrame] using lowSlot
  have actualHigh : (vector128SavedFrame frame slots right).locals[11]? = some (.bytes .vector128 highHome) := by
    simpa [vector128SavedFrame] using highSlot
  apply vector128_output_dispatch current output (vector128SavedFrame frame slots right) args outputArg
    (currentCall.output_formed outputMember) post
  apply vector128_early_output original entered current inputs outputs output
    (vector128SavedFrame frame slots right) args call currentCall outputMember authority outputArg
    (vector128SnapshotValue original left right 9) (vector128SnapshotValue original left right 10)
    lowHome highHome actualLow actualHigh (homes.home_bound 10 .vector128 highHome highSlot) lowRead highRead post
  intro after outputRead afterCall afterAuthority outside privateReads next unchanged
  have retained : ∀ i : Fin 11, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, privateReads reference 16 1 _
      (homes.home_bound i.val .vector128 reference slot) loaded⟩
  exact continuation after retained outputRead afterCall afterAuthority
    (fun id offset old excluded => (outside id offset excluded).trans (preserved.cells id old offset))
    (Nat.le_trans advanced next)
    (fun disabled => by rw [unchanged disabled]; exact preserved)

#print axioms vector128_output_prefix
end UInt256Proof.Add.Safety
