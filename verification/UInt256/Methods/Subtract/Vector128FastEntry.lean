import UInt256.Methods.Subtract.Vector128FastOutput
import UInt256.Methods.Subtract.Vector128FastArithmetic
import UInt256.Safety.HalfOutputValue
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_fast_entry (original entered : Memory)
    (left right output : Reference) (frame : Frame) (slots : List LocalSlot)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame vector128Body (binaryArguments left right output) original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (fast : vector128InitialPropagation original left right = BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ SubtractResult original final returned left right output := by
  let args := binaryArguments left right output
  let post := fun final returned => SubtractResult original final returned left right output
  let values := vector128IncomingValue (vector128InputValues original left right)
  apply vector128_dispatch original entered [left, right] [output] left right frame slots args
    call setup layout homes (by simp) (by simp) (by rfl) (by rfl) post
  intro current snapshots preserved currentCall authority advanced
  simp only [fast, ite_true]
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 4
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 5
  obtain ⟨incomingLowHome, incomingLowSlot, incomingLowRead⟩ := snapshots 8
  obtain ⟨incomingHighHome, incomingHighSlot, incomingHighRead⟩ := snapshots 9
  obtain ⟨maskHome, maskSlot, maskRead⟩ := snapshots 7
  apply vector128_fast_output original entered current [left, right] [output] output
    (vector128SavedFrame frame slots right) args call currentCall (by simp) authority (by rfl)
    (values 4) (values 5) (values 8) (values 9) lowHome highHome incomingLowHome incomingHighHome
    lowSlot highSlot (homes.home_bound 5 .vector128 highHome highSlot) lowRead highRead
    incomingLowSlot incomingHighSlot (homes.home_bound 9 .vector128 incomingHighHome incomingHighSlot)
    incomingLowRead incomingHighRead post
  intro after outputRead afterCall afterAuthority outside privateReads next
  have saved := privateReads maskHome 16 1 _ (homes.home_bound 7 .vector128 maskHome maskSlot) maskRead
  have teardown := leaveFrame_preserves_memory_below (vector128SavedFrame frame slots right) after original.nextIdentity
    (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1)
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed (by simp : output ∈ [output]))
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans outputRead.1
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans outputRead.2
  change read _ output 16 1 = .ok (numberBytes (vector128Corrected original left right false).toNat 16) at lo
  change read _ { output with offset := output.offset + 16 } 16 1 =
    .ok (numberBytes (vector128Corrected original left right true).toNat 16) at hi
  rw [vector128_corrected_difference original left right false fast] at lo
  rw [vector128_corrected_difference original left right true fast] at hi
  refine ⟨7, leaveFrame (vector128SavedFrame frame slots right) after,
    [.scalar (.i32 (vector128FastFlag original left right))], ?_, ?_⟩
  · exact vector128_fast_return after (vector128SavedFrame frame slots right) args maskHome (values 7) maskSlot saved
  · refine ⟨leaveFrame_preserves_wellFormed _ _ afterCall.1.1, ?_, ?_, ?_, ?_⟩
    · have computed := output_value_of_packed_halves _ output (scalarDifferenceWord original left right) lo hi
      exact computed.trans (scalar_difference_value original left right)
    · rw [vector128_fast_flag original left right fast]
    · exact (teardown.access output old 32 1 true).trans
        (afterCall.1.2.2 (wordView output) (by simp))
    · intro id earlier offset untouched
      exact (teardown.cells id earlier offset).trans
        ((outside id offset untouched).trans (preserved.cells id earlier offset))

#print axioms vector128_fast_entry
end UInt256Proof.Subtract.Safety
