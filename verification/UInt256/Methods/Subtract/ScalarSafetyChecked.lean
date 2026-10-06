import UInt256.Methods.Subtract.ScalarBorrowSegments
import UInt256.Methods.Subtract.BorrowArithmetic
import UInt256.Methods.Subtract.ScalarBorrowPrefix
import UInt256.Methods.Add.StorageCall
import CIL.Safety.ReturnMemory
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Subtract.ScalarSmallChecked

namespace UInt256Proof.Subtract.Safety

open CIL.Safety

def scalarStoreCall : Nat :=
  scalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.storeLimbsIndex
    | _ => false

theorem scalar_store_prefix (left right output : Reference)
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 2]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarStoreCall
        (UInt256Model.Safety.binaryArguments left right output)
        frame [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
        (UInt256Model.Safety.binaryArguments left right output)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  conv in (scalarBorrowCall _) => cbv
  simp only [Nat.reduceAdd]
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
    | apply run_next_exists post
      · exact found
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [UInt256Model.Safety.binaryArguments, step, checkedValue, formValue, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩


theorem scalar_return (args : List Value) (frame : Frame) (memory : Memory)
    (borrowHome : Reference) (borrow : BitVec 64)
    (slot : frame.locals[1]? = some (.bytes .word64 borrowHome))
    (loaded : read memory borrowHome 8 1 = .ok (numberBytes borrow.toNat 8)) :
    run Extracted.program (scalarBody.code.length + 1) scalarIndex
      (scalarStoreCall + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (scalarUnderflowFlag borrow))]) := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  conv in scalarBody.code.length => cbv
  conv in scalarStoreCall => cbv
  have tailMetadata : scalarBody.code[scalarStoreCall + 5]? = some .ret ∧ scalarBody.returnsValue = true := by
    constructor <;> rfl
  conv at tailMetadata in scalarStoreCall => cbv
  simp only [Nat.reduceAdd] at tailMetadata
  have reading := load_local_word64_of_read loaded
  simp only [Nat.reduceAdd]
  repeat'
    first
    | apply Eq.trans
      · apply run_next
        · exact found
        · rfl
        · simp (config := { implicitDefEqProofs := false })
            [found, step, slot, reading, checkedValue, numericValue,
              pureArity, scalars, CIL.step, CIL.binary, instruction,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [found, tailMetadata.1, tailMetadata.2, step, checkedValue, numericValue, scalarUnderflowFlag,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_return
#print axioms scalar_store_prefix
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety

/-- Finish the extracted general scalar path, preserving the private borrow
    across output writes and the original caller footprint across teardown. -/
theorem scalar_finish (original entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) original = .ok (frame, entered))
    (state : ScalarBorrowState original current frame left right output borrowHome results 4) :
    ∃ fuel final values,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
        (binaryArguments left right output) frame [] current = .ok (final, values) ∧
      ScalarResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => ScalarResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply scalar_store_prefix left right output frame current results words
    formed state.resultSlots (fun i => state.completed i i.isLt) post
  apply UInt256Proof.Safety.run_store_limbs [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := scalarBody) (op := .call Extracted.storeLimbsIndex 5)
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
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨scalarBody.code.length + 1, leaveFrame frame stored,
      [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))],
      scalar_return _ _ _ _ _ state.borrowSlot borrowRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, rfl, ?_, ?_⟩
    · simpa only [inputValue, bytes, scalarDifferenceValue] using value
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms scalar_finish

end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Complete checked invocation of the large-right scalar branch, including
    initial-input arithmetic, the exact borrow and caller storage preservation. -/
theorem scalar_general_checked (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (large : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ ScalarResult memory final values left right output := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    scalar_frame_setup memory (binaryArguments left right output) call.1.1
  obtain ⟨fuel, final, values, finished, satisfied⟩ := scalar_general_borrows memory entered left right output
    frame call setup homes large (fun final values => ScalarResult memory final values left right output)
    (fun borrowHome results current state =>
      scalar_finish memory entered current frame left right output borrowHome results call setup state)
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  exact ⟨fuel, final, values,
    by simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished,
    satisfied⟩

#print axioms scalar_general_checked
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

theorem ScalarResult.as_subtract {original final : Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    SubtractResult original final values left right output :=
  ⟨result.wellFormed, result.modular_difference,
    by simpa only [scalar_flag_underflow, subtractUnderflow] using result.flag,
    result.writable, result.footprint⟩

theorem scalar_checked (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ SubtractResult memory final values left right output := by
  by_cases small : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 = BitVec.ofNat 64 0
  · exact scalar_right_small_checked memory left right output call small
  · obtain ⟨fuel, final, values, executed, result⟩ := scalar_general_checked memory left right output call small
    exact ⟨fuel, final, values, executed, result.as_subtract⟩

#print axioms ScalarResult.as_subtract
#print axioms scalar_checked
end UInt256Proof.Subtract.Safety
