import UInt256.Methods.Add.Vector128SSEFinish
import UInt256.Methods.Add.Vector128RepairDispatch

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

/-- The complete SSE repair route from helper entry, including initial-input
    arithmetic, exact overflow and preservation outside an arbitrarily aliased output. -/
theorem vector128_sse_repair_entry (original entered : CIL.Safety.Memory)
    (left right output : Reference) (frame : Frame) (slots : List LocalSlot)
    (flag : BitVec 32)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame vector128Body
      (binaryArguments left right output ++ [.scalar (.i32 flag)]) original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (repair : selectedPropagation128 flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) ≠ BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0
        (binaryArguments left right output ++ [.scalar (.i32 flag)]) frame [] entered =
          .ok (final, returned) ∧ AddResult original final returned left right output := by
  let args := binaryArguments left right output ++ [.scalar (.i32 flag)]
  let post := fun final returned => AddResult original final returned left right output
  apply vector128_dispatch_checked original entered [left, right] [output] left right output
    frame slots args call setup layout homes (by simp) (by simp) (by simp)
    (by rfl) (by rfl) (by rfl) flag (by rfl) post
  intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced preserved
  simp only [repair, ite_false]
  apply vector128_repair_dispatch current (vector128SavedFrame frame slots right) args post
  change ∃ fuel final returned,
    run Extracted.program fuel vector128Index 162 args (vector128SavedFrame frame slots right) [] current =
      .ok (final, returned) ∧ post final returned
  apply vector128_sse_repair_carry original entered current (vector128SavedFrame frame slots right)
    (.root (some (.address right))) slots rfl left right output call currentCall (preserved (by rfl))
    homes (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) authority [.scalar (.i32 flag)] post
  intro carryHome results after state
  exact vector128_sse_finish original after (vector128SavedFrame frame slots right)
    left right output carryHome results [.scalar (.i32 flag)] call
    (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1) state

#print axioms vector128_sse_repair_entry
end UInt256Proof.Add.Safety
