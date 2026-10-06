import UInt256.Methods.Shift.SafetyStore

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- From the prepared private snapshots, finish the selected shift, including
    the real storage call and normal return. -/
theorem shift_nonzero_finish (whole : Fin 4) (memory : Memory) (frame : Frame)
    (inputs : List Reference) (args : List Value) (output : Reference) (count : BitVec 32)
    (wholeHome maskHome complementHome : Reference)
    (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64) (boundary : Nat)
    (argument : args[2]? = some (.reference (.address output)))
    (call : CallingConditions Extracted.program memory inputs [output])
    (wholeSlot : frame.locals[0]? = some (.bytes .word32 wholeHome))
    (maskSlot : frame.locals[1]? = some (.bytes .word32 maskHome))
    (complementSlot : frame.locals[2]? = some (.bytes .word32 complementHome))
    (wholeRead : read memory wholeHome 4 1 = .ok (numberBytes whole.val 4))
    (maskRead : read memory maskHome 4 1 = .ok (numberBytes (count &&& (63 : BitVec 32)).toNat 4))
    (complementRead : read memory complementHome 4 1 =
      .ok (numberBytes ((63 : BitVec 32) - (count &&& 63)).toNat 4))
    (slots : ∀ i : Fin 4, frame.locals[3 + i.val]? = some (.bytes .word64 (homes i)))
    (reads : ∀ i : Fin 4, read memory (homes i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 39) args frame [] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧
      inputValue final output = shiftValue shiftDirection (UInt256Model.value words) (64 * whole.val + count.toNat % 64) ∧
      access final output 32 1 true = .ok () ∧
      (∃ bytes, read final output 32 1 = .ok bytes) ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  apply shift_output_dispatch whole memory frame args wholeHome wholeSlot wholeRead
  apply shift_output_arguments whole memory frame args output (count &&& 63) (63 - (count &&& 63))
    maskHome complementHome homes words argument (call.output_formed (by simp))
    maskSlot complementSlot maskRead complementRead slots reads
  let outputWords := outputWords shiftDirection whole words (count &&& 63) (63 - (count &&& 63))
  obtain ⟨fuel, final, returned, executed, empty, wf, result, writable, readable, footprint⟩ :=
    shift_store_return whole memory inputs frame args output boundary
      (outputWords.getD 0 0) (outputWords.getD 1 0) (outputWords.getD 2 0) (outputWords.getD 3 0)
      call outputOld owned
  have stack : outputWords.reverse.map (fun w => Value.scalar (.i64 w)) =
      [.scalar (.i64 (outputWords.getD 3 0)), .scalar (.i64 (outputWords.getD 2 0)),
       .scalar (.i64 (outputWords.getD 1 0)), .scalar (.i64 (outputWords.getD 0 0))] := by
    have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
    cases shiftDirection <;> rcases cases with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨fuel, final, returned, ?_, empty, wf, ?_, writable, readable, footprint⟩
  · change run _ _ _ _ _ _ (outputWords.reverse.map _ ++ _) _ = _
    rw [stack]
    exact executed
  · have packed := pack_value (fun i : Fin 4 => outputWords.getD i.val 0)
    change pack (outputWords.getD 0 0) (outputWords.getD 1 0)
      (outputWords.getD 2 0) (outputWords.getD 3 0) = _ at packed
    exact result.trans (packed.symm.trans (shift_output_value shiftDirection whole words count))

#print axioms shift_nonzero_finish
end UInt256Proof.Shift.Safety
