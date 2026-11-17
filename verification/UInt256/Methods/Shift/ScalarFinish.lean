import UInt256.Methods.Shift.ScalarReturn

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
  (store : StoreLimbsContract program storage)
include bodyFound store
/-- From the prepared private snapshots, finish the selected shift, including
    the real storage call and normal return. -/
theorem shift_nonzero_finish (whole : Fin 4) (original entered memory : Memory)
    (input output : Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (words : Fin 4 → BitVec 64) (known : Nat → Option CIL.Value) (boundary : Nat)
    (argument : args[2]? = some (.reference (.address output)))
    (state : VectorFrame program original entered memory [input] output frame
      (preparedLocals known count words) none)
    (wholeKnown : known 0 = some (.i32 (BitVec.ofNat 32 whole.val)))
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run program fuel index (39) args frame [] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧
      inputValue final output = shiftValue direction (UInt256Model.value words) (64 * whole.val + count.toNat % 64) ∧
      access final output 32 1 true = .ok () ∧
      (∃ bytes, read final output 32 1 = .ok bytes) ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  apply shift_output_arguments bodyFound whole original entered memory input output frame args
    count words known argument state wholeKnown
  let outputWords := outputWords direction whole words (count &&& 63) (63 - (count &&& 63))
  obtain ⟨fuel, final, returned, executed, empty, wf, result, writable, readable, footprint⟩ :=
    shift_store_return bodyFound store whole memory [input] frame args output boundary
      (outputWords.getD 0 0) (outputWords.getD 1 0) (outputWords.getD 2 0) (outputWords.getD 3 0)
      state.call outputOld owned
  have stack : outputWords.reverse.map (fun w => Value.scalar (.i64 w)) =
      [.scalar (.i64 (outputWords.getD 3 0)), .scalar (.i64 (outputWords.getD 2 0)),
       .scalar (.i64 (outputWords.getD 1 0)), .scalar (.i64 (outputWords.getD 0 0))] := by
    have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
    cases direction <;> rcases cases with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨fuel, final, returned, ?_, empty, wf, ?_, writable, readable, footprint⟩
  · change run _ _ _ _ _ _ (outputWords.reverse.map _ ++ _) _ = _
    rw [stack]
    exact executed
  · have packed := pack_value (fun i : Fin 4 => outputWords.getD i.val 0)
    change pack (outputWords.getD 0 0) (outputWords.getD 1 0)
      (outputWords.getD 2 0) (outputWords.getD 3 0) = _ at packed
    exact result.trans (packed.symm.trans (shift_output_value direction whole words count))

end UInt256Proof.Shift.Safety
