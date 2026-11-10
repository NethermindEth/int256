import CIL.Safety.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.Subtract.BorrowContract
import UInt256.Methods.Subtract.SafetyResult
import UInt256.Methods.AddSubtract.Vector128Inputs
import UInt256.Methods.Multiply.LimbStorage
import UInt256.Methods.AddSubtract.Vector128Ripple
import CIL.Safety.CallComposition

namespace UInt256Proof.Subtract.Profile
def subtractRepairCode (borrow storage : Nat) : List CIL.Op := [
  .const32 0, .convI8, .setLocal 11,
  .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .localAddr 11, .localAddr 12, .call borrow 4,
  .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .localAddr 11, .localAddr 13, .call borrow 4,
  .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .localAddr 11, .localAddr 14, .call borrow 4,
  .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .localAddr 11, .localAddr 15, .call borrow 4,
  .arg 2, .local 12, .local 13, .local 14, .local 15, .call storage 5,
  .local 11, .const32 0, .convI8, .gtu, .ret (some .unsigned8)]

def subtractWordSpec : CIL.Safety.NumericLocalSpec := ⟨.word64, .i64 0, 0, rfl⟩
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Advance the borrow invariant through one actual repair call. -/
theorem subtract_repair_next (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (borrow storage : Nat) (code : CodeAt body 77 (subtractRepairCode borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarBorrowState (program := program) original before frame left right output borrowHome results index.val 11 12)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState (program := program) original after frame left right output borrowHome results (index.val + 1) 11 12 →
      ∃ fuel result returned,
        run program fuel method (87 + 7 * index.val) args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method (80 + 7 * index.val) args frame [] before =
        .ok (result, returned) ∧ post result returned := by
  apply ripple_limb borrowContract program body method found borrow storage 77 10 code
    (borrow_helper_contract borrowFound)
    ⟨inputLimb before left index, inputLimb before right index,
      scalarBorrowValue original left right index.val, borrowHome, results index⟩
    index left right output args leftArg rightArg frame before borrowHome (results index) state.call
    state.borrowSlot (by simpa [Nat.add_comm] using state.resultSlots index) rfl (fun _ => rfl)
    ⟨state.call.1.1, state.borrowBound, state.borrowRead, state.borrowWrite, state.resultWrites index,
      Or.inl (Ne.symm (state.borrowSeparate index))⟩ state.borrowWrite (state.resultWrites index) post
  intro after _ formed world framed math
  apply continuation after
  refine state.advance index ?_ formed world framed
  simpa only [borrowContract, inputLimb, state.inputBytes left (by simp), state.inputBytes right (by simp)] using math

/-- All four borrow calls keep the initial operands, private homes and completed limbs. -/
theorem subtract_repair_all (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (borrow storage : Nat) (code : CodeAt body 77 (subtractRepairCode borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarBorrowState (program := program) original before frame left right output borrowHome results 0 11 12)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState (program := program) original after frame left right output borrowHome results 4 11 12 →
      ∃ fuel result returned,
        run program fuel method 108 args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 80 args frame [] before = .ok (result, returned) ∧ post result returned := by
  apply subtract_repair_next program body method found borrow storage code borrowFound
    0 state args leftArg rightArg post
  intro _ first
  apply subtract_repair_next program body method found borrow storage code borrowFound
    1 first args leftArg rightArg post
  intro _ second
  apply subtract_repair_next program body method found borrow storage code borrowFound
    2 second args leftArg rightArg post
  intro _ third
  exact subtract_repair_next program body method found borrow storage code borrowFound
    3 third args leftArg rightArg post continuation

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The five repair word homes are fresh and keep write authority through the vector prefix. -/
theorem subtract_repair_word_home (specs : List NumericLocalSpec)
    (wordSpecs : ∀ i : Fin 5, specs[10 + i.val]? = some subtractWordSpec) (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) (index : Fin 5) :
    ∃ reference,
      slots[10 + index.val]? = some (.bytes .word64 reference) ∧
      frame.locals[11 + index.val]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧
      access current reference 8 1 true = .ok () := by
  obtain ⟨reference, slot, fresh, _, writable⟩ := homes.home_at _ _ (wordSpecs index)
  change slots[10 + index.val]? = some (.bytes .word64 reference) at slot
  have actual : frame.locals[11 + index.val]? = some (.bytes .word64 reference) := by
    simpa [layout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using slot
  obtain ⟨allocation, ready⟩ := access_requirements writable
  exact ⟨reference, slot, actual, fresh, authority.access writable (enteredWF.1 _ _ ready.present).1⟩

/-- Build the zero-borrow invariant from fresh private homes and unchanged caller memory. -/
theorem subtract_repair_ready (program : CIL.Program) (specs : List NumericLocalSpec)
    (wordSpecs : ∀ i : Fin 5, specs[10 + i.val]? = some subtractWordSpec) (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output borrowHome : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (borrowSlot : frame.locals[11]? = some (.bytes .word64 borrowHome))
    (borrowRead : read current borrowHome 8 1 = .ok (numberBytes 0 8)) :
    ∃ results : Fin 4 → Reference,
      ScalarBorrowState (program := program) original current frame left right output borrowHome results 0 11 12 := by
  classical
  have allHomes := subtract_repair_word_home specs wordSpecs original entered current frame root slots layout homes enteredWF authority
  obtain ⟨borrowRef, borrowLocal, actualBorrow, borrowFresh, borrowWrite⟩ := allHomes 0
  have same : borrowRef = borrowHome := by simpa only [show 11 + (0 : Fin 5).val = 11 from rfl, borrowSlot,
    Option.some.injEq, LocalSlot.bytes.injEq, true_and] using actualBorrow.symm
  subst borrowRef
  let results : Fin 4 → Reference := fun i => Classical.choose (allHomes ⟨i.val + 1, by omega⟩)
  have resultFacts (i : Fin 4) := Classical.choose_spec (allHomes ⟨i.val + 1, by omega⟩)
  have resultSlots (i : Fin 4) : slots[11 + i.val]? = some (.bytes .word64 (results i)) := by
    have found := (resultFacts i).1
    change slots[10 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  have ordered (i : Fin 4) : borrowHome.allocation < (results i).allocation :=
    homes.ordered 10 (11 + i.val) .word64 .word64 borrowHome (results i) (by omega) borrowLocal (resultSlots i)
  refine ⟨results, currentCall, ?_, borrowSlot, ?_, borrowWrite, ?_, borrowRead, by simp [scalarBorrowValue],
    ?_, (fun i => Ne.symm (Nat.ne_of_lt (ordered i))), ?_, borrowFresh, ?_, preserved.cells, ?_⟩
  · intro reference member
    exact call.input_bytes_of_memory_below preserved member
  · intro i
    have found := (resultFacts i).2.1
    change frame.locals[11 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  · intro i
    exact (resultFacts i).2.2.2
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old : reference.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old borrowFresh),
      fun i => Nat.ne_of_lt (Nat.lt_of_lt_of_le old (resultFacts i).2.2.1)⟩
  · intro i j different
    have distinct : i.val ≠ j.val := fun equal => different (Fin.ext equal)
    by_cases before : i.val < j.val
    · exact Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots i) (resultSlots j))
    · exact Ne.symm (Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots j) (resultSlots i)))
  · intro i
    exact (resultFacts i).2.2.1
  · intro i impossible
    omega

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- From pc 77, zero the borrow and run all four checked borrow calls on the initial limbs. -/
theorem subtract_repair_borrow (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (borrow storage : Nat) (code : CodeAt body 77 (subtractRepairCode borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody body.profile))
    (wordSpecs : ∀ i : Fin 5, specs[10 + i.val]? = some subtractWordSpec)
    (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ borrowHome results after,
      ScalarBorrowState (program := program) original after frame left right output borrowHome results 4 11 12 →
      ∃ fuel final returned,
        run program fuel method 108 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 77 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply ripple_start program body method specs found borrow storage 77 10 code
    (wordSpecs 0) original.nextIdentity entered current [left, right] [output]
    frame root slots layout args currentCall enteredWF homes authority post
  intro borrowHome after borrowSlot borrowRead retained afterCall afterAuthority _written
  obtain ⟨results, ready⟩ := subtract_repair_ready program specs wordSpecs original entered after frame root slots layout
    left right output borrowHome call afterCall (preserved.trans retained) homes enteredWF afterAuthority borrowSlot borrowRead
  exact subtract_repair_all program body method found borrow storage code borrowFound
    ready args leftArg rightArg post (continuation borrowHome results)

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety

/-- Store the four ripple words through the checked limb helper and return the exact borrow. -/
theorem subtract_repair_finish (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (borrow storage : Nat) (code : CodeAt body 77 (subtractRepairCode borrow storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (returns : body.returnsValue = true)
    (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarBorrowState (program := program) original current frame left right output borrowHome results 4 11 12) :
    ∃ fuel final values,
      run program fuel method 108 args frame [] current = .ok (final, values) ∧
      SubtractResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => SubtractResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply ripple_store_prefix program body method found borrow storage 77 10 code
    output args outputArg frame current results words formed
    (fun i => by simpa [Nat.add_comm] using state.resultSlots i) (fun i => state.completed i i.isLt) post
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract body.profile program storage storageFound
      current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) 113 args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3)) [] current) := by
    simp [step, cil_guard, observerCount, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  obtain ⟨borrowAllocation, borrowPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.borrowWrite
  have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
  have distinct : borrowHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.borrowFresh))
  have borrowRead := authority.read_eq state.borrowRead borrowOld
    (fun i _ => outside _ _ (Or.inl distinct))
  have returned : run program 5 method 114 args frame [] stored =
      .ok (leaveFrame frame stored, [.scalar (.i32 (scalarUnderflowFlag _))]) :=
    ripple_return program body method found borrow storage 77 10 code returns
      args frame stored borrowHome _ state.borrowSlot borrowRead
  obtain ⟨fuel, executed⟩ := run_call_exists found
    (by (conv => lhs; arg 2; whnf); cil_lookup [code]) stepped ⟨childFuel, invoked⟩ ⟨5, returned⟩
  refine ⟨fuel, leaveFrame frame stored, _, executed, ?_⟩
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity owned
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

end UInt256Proof.Subtract.Profile
