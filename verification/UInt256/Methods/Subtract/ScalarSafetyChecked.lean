import UInt256.Methods.Subtract.ScalarBorrowSegments
import UInt256.Methods.Subtract.BorrowArithmetic
import UInt256.Methods.Subtract.ScalarBorrowPrefix
import UInt256.Safety.StorageSelection
import CIL.Safety.ReturnMemory
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Subtract.ScalarSmallChecked

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Proof.Subtract.Profile

def scalarStoreCall : Nat :=
  scalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.storeLimbsIndex
    | _ => false

theorem scalar_store_prefix (left right output : Reference)
    (frame : Frame) (memory : Memory) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (snapshots : LocalSnapshots memory frame.locals
      (UInt256Proof.AddSubtract.Safety.completedLocals words 2 4))
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
  have loading (i : Fin 4) (pc : Nat) (stack : List Value) := snapshots.load
    (body := scalarBody) (args := UInt256Model.Safety.binaryArguments left right output)
    (pc := pc) (stack := stack) (index := i.val + 2) (.i64 (words i))
    (by simp [UInt256Proof.AddSubtract.Safety.completedLocals, i.isLt])
  iterate 5
    apply run_next_exists post found
    · rfl
    · first
      | exact loading 0 _ _
      | exact loading 1 _ _
      | exact loading 2 _ _
      | exact loading 3 _ _
      | cil_checked_step [UInt256Model.Safety.binaryArguments, outputFormed]
  exact continuation
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
  have tailMetadata : scalarBody.code[scalarStoreCall + 5]? = some (.ret (some .unsigned8)) ∧ scalarBody.returnsValue = true := by
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
            [found, step, cil_guard, observerCount, slot, reading, checkedValue, numericValue,
              pureArity, scalars, CIL.step, CIL.binary, CIL.unary, instruction,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [found, tailMetadata.1, tailMetadata.2, step, cil_guard, observerCount, checkedValue, numericValue, scalarUnderflowFlag, CIL.NarrowKind.extend,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

  simp [run, found, tailMetadata.1, tailMetadata.2, step, cil_guard, observerCount, checkedValue, numericValue,
    scalarUnderflowFlag, CIL.NarrowKind.extend, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  split <;> rfl

#print axioms scalar_return
#print axioms scalar_store_prefix
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Profile

/-- Finish the extracted general scalar path, preserving the private borrow
    across output writes and the original caller footprint across teardown. -/
theorem scalar_finish (original entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) original = .ok (frame, entered))
    (state : ScalarBorrowState (program := Extracted.program) original current frame left right output borrowHome results 4) :
    ∃ fuel final values,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
        (binaryArguments left right output) frame [] current = .ok (final, values) ∧
      ScalarResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => ScalarResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply scalar_store_prefix left right output frame current words
    formed state.snapshots post
  apply UInt256Proof.Safety.run_store_limbs UInt256Proof.Safety.storage_contract [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := scalarBody) (op := .call Extracted.storeLimbsIndex 5)
  · rfl
  · rfl
  · unfold UInt256Proof.Safety.storageArguments
    repeat' (conv in UInt256Proof.Safety.storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl⟩
  · exact state.call
  · intro stored valid outside authority value
    obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have outputOld := (call.1.1.1 _ _ outputPresent).1
    obtain ⟨borrowAllocation, borrowPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.flagWrite
    have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
    have distinct : borrowHome.allocation ≠ output.allocation :=
      Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.flagFresh))
    have borrowRead := authority.read_eq state.flagRead borrowOld
      (fun i _ => outside _ _ (Or.inl distinct))
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨scalarBody.code.length + 1, leaveFrame frame stored,
      [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))],
      scalar_return _ _ _ _ _ state.flagSlot borrowRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, rfl, ?_, ?_⟩
    · simpa only [inputValue, bytes, scalarDifferenceValue] using value
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.writable (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms scalar_finish

end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Profile

/-- Complete checked invocation of the large-right scalar branch, including
    initial-input arithmetic, the exact borrow and caller storage preservation. -/
theorem scalar_general_checked (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (large : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ ScalarResult memory final values left right output := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    scalar_frame_setup memory (binaryArguments left right output) call.1.1
  obtain ⟨fuel, final, values, finished, satisfied⟩ := scalar_general_borrows contract memory entered left right output
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
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Profile

theorem ScalarResult.as_subtract {original final : Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    SubtractResult original final values left right output :=
  ⟨result.wellFormed, result.modular_difference,
    by simpa only [scalar_flag_underflow, subtractUnderflow] using result.flag,
    result.writable, result.footprint⟩

theorem scalar_checked (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ SubtractResult memory final values left right output := by
  by_cases small : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 = BitVec.ofNat 64 0
  · exact scalar_right_small_checked memory left right output call small
  · obtain ⟨fuel, final, values, executed, result⟩ := scalar_general_checked contract memory left right output call small
    exact ⟨fuel, final, values, executed, result.as_subtract⟩

#print axioms ScalarResult.as_subtract
#print axioms scalar_checked
end UInt256Proof.Subtract.Safety
