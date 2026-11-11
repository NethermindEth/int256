import UInt256.Methods.Subtract.ScalarBorrowSegments
import UInt256.Methods.Subtract.BorrowArithmetic
import UInt256.Methods.Subtract.ScalarBorrowPrefix
import UInt256.Safety.StorageSelection
import CIL.Safety.ReturnMemory
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Subtract.ScalarSmallChecked

/-! The extracted scalar Subtract body: the large-right route stores its four borrow-chain
    words and returns the final borrow; either route gives the exact difference and flag. -/

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Profile

def scalarStoreCall : Nat :=
  scalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.storeLimbsIndex
    | _ => false

/-- Complete checked invocation of the large-right scalar branch, including
    initial-input arithmetic, the exact borrow and caller storage preservation. The private
    borrow survives the output writes and the caller footprint survives teardown. -/
theorem scalar_general_checked (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (large : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ ScalarResult memory final values left right output := by
  let words := scalarDifferenceWord memory left right
  let post := fun final values => ScalarResult memory final values left right output
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    scalar_frame_setup memory (binaryArguments left right output) call.1.1
  obtain ⟨fuel, final, values, finished, satisfied⟩ := scalar_general_borrows contract memory
    entered left right output frame call setup homes large post (by
      intro borrowHome results current state
      have formed := state.call.output_formed (by simp : output ∈ [output])
      have stored : ∃ fuel result returned,
          run Extracted.program fuel scalarIndex scalarStoreCall
            (binaryArguments left right output) frame
            [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
              .scalar (.i64 (words 0)), .reference (.address output)] current =
              .ok (result, returned) ∧
            post result returned := by
        apply UInt256Proof.Safety.run_store_limbs UInt256Proof.Safety.storage_contract
          [left, right] output (words 0) (words 1) (words 2) (words 3) post (body := scalarBody)
          (op := .call Extracted.storeLimbsIndex 5)
        · rfl
        · rfl
        · unfold UInt256Proof.Safety.storageArguments
          repeat' (conv in UInt256Proof.Safety.storageWordOrder => cbv)
          simp [List.range_succ, List.findIdx, List.findIdx.go, step, cil_guard, observerCount,
            checkedValue, numericValue, formValue, formed, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact ⟨rfl, rfl, rfl⟩
        · exact state.call
        · intro stored valid outside authority value
          obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
            (call.output_formed (by simp : output ∈ [output]))
          have outputOld := (call.1.1.1 _ _ outputPresent).1
          obtain ⟨borrowAllocation, borrowPresent, _, _⟩ :=
            access_within_allocation _ _ _ _ _ state.flagWrite
          have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
          have distinct : borrowHome.allocation ≠ output.allocation :=
            Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.flagFresh))
          have borrowRead := authority.read_eq state.flagRead borrowOld
            (fun i _ => outside _ _ (Or.inl distinct))
          have fresh := enterFrame_fresh _ _ _ _ _ setup
          have retained := leaveFrame_preserves_memory_below frame stored memory.nextIdentity
            (fun id member => (fresh.2 id member).1)
          have bytes : (fun offset =>
              ((leaveFrame frame stored).cells output.allocation offset).bits) =
              (fun offset => (stored.cells output.allocation offset).bits) := by
            funext offset
            rw [retained.cells output.allocation outputOld offset]
          have result : post (leaveFrame frame stored)
              [.scalar (.i32 (CIL.NarrowKind.unsigned8.extend
                (scalarUnderflowFlag (scalarBorrowValue memory left right 4))))] :=
            ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1,
              by simpa only [inputValue, bytes, scalarDifferenceValue] using value,
              congrArg (fun flag => [Value.scalar (.i32 flag)])
                (CIL.NarrowKind.extend_ite_one_zero _ _),
              (retained.access output outputOld 32 1 true).trans
                (valid.1.writable (wordView output) (by simp)),
              fun id old offset untouched => (retained.cells id old offset).trans
                ((outside id offset untouched).trans (state.callerCells id old offset))⟩
          conv in scalarStoreCall => cbv
          cil_contract_steps [found, state.flagSlot, load_local_word64_of_read borrowRead]
          exact result
      conv in (scalarBorrowCall _) => cbv
      conv at stored in scalarStoreCall => cbv
      cil_contract_steps (snapshots := state.snapshots)
        [found, binaryArguments, formed, UInt256Proof.AddSubtract.Safety.completedLocals]
      exact stored)
  exact ⟨fuel, final, values, invoke_of_run found
    (checkedValues_of_valid call.binary_arguments_valid) setup finished, satisfied⟩

/-- Either route of the extracted scalar body: the exact difference and underflow flag of the
    initial operands, a writable output and every other caller byte kept. -/
theorem scalar_checked (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel scalarIndex (binaryArguments left right output) memory =
        .ok (final, values) ∧ SubtractResult memory final values left right output := by
  by_cases small : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 = BitVec.ofNat 64 0
  · exact scalar_right_small_checked memory left right output call small
  · obtain ⟨fuel, final, values, executed, result⟩ :=
      scalar_general_checked contract memory left right output call small
    exact ⟨fuel, final, values, executed, result.wellFormed, result.modular_difference,
      by simpa only [scalar_flag_underflow, subtractUnderflow] using result.flag,
      result.writable, result.footprint⟩

end UInt256Proof.Subtract.Safety
