import UInt256.Methods.Subtract.Vector128BorrowSetup
import UInt256.Methods.Add.StorageCall
import UInt256.Methods.Subtract.BorrowArithmetic
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_store_prefix (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 12]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index 113
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 108
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  have s0 := slots 0
  have s1 := slots 1
  have s2 := slots 2
  have s3 := slots 3
  dsimp at s0 s1 s2 s3
  simp only [CIL.fin_val_three, Nat.reduceAdd] at s3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  repeat'
    first
    | exact continuation
    | apply run_next_exists post (by rfl : Extracted.program[vector128Index]? = some vector128Body) (by rfl)
      simp (config := { implicitDefEqProofs := false })
          [cil_code, step, checkedValue, formValue, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem vector128_return (args : List Value) (frame : Frame) (memory : Memory)
    (borrowHome : Reference) (borrow : BitVec 64)
    (slot : frame.locals[11]? = some (.bytes .word64 borrowHome))
    (loaded : read memory borrowHome 8 1 = .ok (numberBytes borrow.toNat 8)) :
    run Extracted.program 5 vector128Index 114 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if BitVec.ofNat 64 0 < borrow then 1 else 0))]) := by
  have reading := load_local_word64_of_read loaded
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  repeat'
    first
    | apply Eq.trans
      · apply run_next found (by rfl)
        simp (config := { implicitDefEqProofs := false })
          [step, slot, reading, checkedValue, numericValue, pureArity, scalars,
            CIL.step, CIL.binary, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [found, show vector128Body.code[118]? = some .ret from rfl,
            show vector128Body.returnsValue = true from rfl, step, checkedValue, numericValue,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_store_prefix
#print axioms vector128_return
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_finish (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference) (extra : List Value)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarBorrowState original current frame left right output borrowHome results 4 11 12) :
    ∃ fuel final values,
      run Extracted.program fuel vector128Index 108
        (binaryArguments left right output ++ extra) frame [] current = .ok (final, values) ∧
      SubtractResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => SubtractResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply vector128_store_prefix left right output extra frame current results words
    formed state.resultSlots (fun i => state.completed i i.isLt) post
  apply run_store_limbs [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := vector128Body) (op := .call Extracted.storeLimbsIndex 5)
  · rfl
  · rfl
  · unfold UInt256Proof.Safety.storageArguments
    repeat' (conv in UInt256Proof.Safety.storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, step, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact state.call
  · intro stored valid outside authority value
    obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have outputOld := (call.1.1.1 _ _ outputPresent).1
    obtain ⟨borrowAllocation, borrowPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.borrowWrite
    have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
    have distinct : borrowHome.allocation ≠ output.allocation :=
      Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.borrowFresh))
    have borrowRead := authority.read_eq state.borrowRead borrowOld
      (fun i _ => outside _ _ (Or.inl distinct))
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      owned
    refine ⟨5, leaveFrame frame stored,
      [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))],
      vector128_return _ _ _ _ _ state.borrowSlot borrowRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
    · have computed : inputValue (leaveFrame frame stored) output = scalarDifferenceValue original left right := by
        simpa only [inputValue, bytes, scalarDifferenceValue] using value
      exact computed.trans (scalar_difference_value original left right)
    · rw [scalar_flag_underflow]
      rfl
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms vector128_finish
end UInt256Proof.Subtract.Safety

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
