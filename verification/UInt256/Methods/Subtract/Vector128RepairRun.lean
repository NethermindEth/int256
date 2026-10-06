import UInt256.Methods.Subtract.Vector128RepairFinish

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The complete repair route proves the initial mathematical difference and
    exact underflow while preserving caller bytes outside the aliased output. -/
theorem vector128_repair_entry (original entered : Memory)
    (left right output : Reference) (frame : Frame) (slots : List LocalSlot)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame vector128Body (binaryArguments left right output) original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (repair : vector128InitialPropagation original left right ≠ BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ SubtractResult original final returned left right output := by
  let args := binaryArguments left right output
  let post := fun final returned => SubtractResult original final returned left right output
  apply vector128_dispatch original entered [left, right] [output] left right frame slots args
    call setup layout homes (by simp) (by simp) (by rfl) (by rfl) post
  intro current snapshots preserved currentCall authority advanced
  simp only [repair, ite_false]
  apply vector128_repair_borrow original entered current (vector128SavedFrame frame slots right)
    (.root (some (.address right))) slots rfl left right output call currentCall preserved
    homes (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) authority [] post
  intro borrowHome results after state
  exact vector128_finish original after (vector128SavedFrame frame slots right)
    left right output borrowHome results [] call
    (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1) state

#print axioms vector128_repair_entry
end UInt256Proof.Subtract.Safety
