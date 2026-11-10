import CIL.Safety.SymbolicExecution
import CIL.Safety.Equations
import UInt256.Methods.Add.CarryContract
import UInt256.Methods.Add.ARMBody
import UInt256.Methods.Multiply.LimbStorage
import UInt256.Methods.AddSubtract.Vector128Ripple
import CIL.Safety.CallComposition
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
def sseRepairCode (carry storage : Nat) : List CIL.Op := [
  .const32 0, .convI8, .setLocal 15,
  .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .localAddr 15, .localAddr 16, .call carry 4,
  .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .localAddr 15, .localAddr 17, .call carry 4,
  .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .localAddr 15, .localAddr 18, .call carry 4,
  .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .localAddr 15, .localAddr 19, .call carry 4,
  .arg 2, .local 16, .local 17, .local 18, .local 19, .call storage 5,
  .local 15, .const32 0, .convI8, .gtu, .ret (some .unsigned8)]
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.CarrySafety

/-- Advance the carry invariant through one actual SSE repair call. -/
theorem vector128_sse_carry_next (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (carry storage : Nat) (code : CodeAt body 162 (sseRepairCode carry storage))
    (carryFound : program[carry]? = some (carryBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarCarryState (program := program) original before frame left right output carryHome results index.val 15 16)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState (program := program) original after frame left right output carryHome results (index.val + 1) 15 16 →
      ∃ fuel result returned,
        run program fuel method (172 + 7 * index.val) args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method (165 + 7 * index.val) args frame [] before =
        .ok (result, returned) ∧ post result returned := by
  apply ripple_limb carryContract program body method found carry storage 162 14 code
    (carry_helper_contract carryFound)
    ⟨inputLimb before left index, inputLimb before right index,
      scalarCarryValue original left right index.val, carryHome, results index⟩
    index left right output args leftArg rightArg frame before carryHome (results index) state.call
    state.flagSlot (by simpa [Nat.add_comm] using state.resultSlots index) rfl (fun _ => rfl)
    ⟨state.call.1.1, state.flagBound, state.flagRead, state.flagWrite, state.resultWrites index,
      Or.inl (Ne.symm (state.flagSeparate index))⟩ state.flagWrite (state.resultWrites index) post
  intro after _ formed world framed math
  apply continuation after
  refine state.advance index ?_ formed world framed
  simpa only [carryContract, inputLimb, state.inputBytes left (by simp), state.inputBytes right (by simp)] using math

/-- All four carry calls keep the initial operands, private homes and completed limbs. -/
theorem vector128_sse_carry_all (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (carry storage : Nat) (code : CodeAt body 162 (sseRepairCode carry storage))
    (carryFound : program[carry]? = some (carryBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarCarryState (program := program) original before frame left right output carryHome results 0 15 16)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState (program := program) original after frame left right output carryHome results 4 15 16 →
      ∃ fuel result returned,
        run program fuel method 193 args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 165 args frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_sse_carry_next program body method found carry storage code carryFound
    0 state args leftArg rightArg post
  intro _ first
  apply vector128_sse_carry_next program body method found carry storage code carryFound
    1 first args leftArg rightArg post
  intro _ second
  apply vector128_sse_carry_next program body method found carry storage code carryFound
    2 second args leftArg rightArg post
  intro _ third
  exact vector128_sse_carry_next program body method found carry storage code carryFound
    3 third args leftArg rightArg post continuation

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.CarrySafety

/-- The five repair word homes are fresh and keep write authority through the vector prefix. -/
theorem vector128_sse_word_home (specs : List NumericLocalSpec)
    (wordSpecs : ∀ i : Fin 5, specs[14 + i.val]? = some armWordSpec) (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) (index : Fin 5) :
    ∃ reference,
      slots[14 + index.val]? = some (.bytes .word64 reference) ∧
      frame.locals[15 + index.val]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧
      access current reference 8 1 true = .ok () := by
  obtain ⟨reference, slot, fresh, _, writable⟩ := homes.home_at _ _ (wordSpecs index)
  change slots[14 + index.val]? = some (.bytes .word64 reference) at slot
  have actual : frame.locals[15 + index.val]? = some (.bytes .word64 reference) := by
    simpa [layout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using slot
  obtain ⟨allocation, ready⟩ := access_requirements writable
  exact ⟨reference, slot, actual, fresh, authority.access writable (enteredWF.1 _ _ ready.present).1⟩

/-- Build the zero-carry invariant from fresh private homes and unchanged caller memory. -/
theorem vector128_sse_carry_ready (program : CIL.Program) (specs : List NumericLocalSpec)
    (wordSpecs : ∀ i : Fin 5, specs[14 + i.val]? = some armWordSpec) (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output carryHome : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (carryRead : read current carryHome 8 1 = .ok (numberBytes 0 8)) :
    ∃ results : Fin 4 → Reference,
      ScalarCarryState (program := program) original current frame left right output carryHome results 0 15 16 := by
  classical
  have allHomes := vector128_sse_word_home specs wordSpecs original entered current frame root slots layout homes enteredWF authority
  obtain ⟨carryRef, carryLocal, actualCarry, carryFresh, carryWrite⟩ := allHomes 0
  have same : carryRef = carryHome := by simpa only [show 15 + (0 : Fin 5).val = 15 from rfl, carrySlot,
    Option.some.injEq, LocalSlot.bytes.injEq, true_and] using actualCarry.symm
  subst carryRef
  let results : Fin 4 → Reference := fun i => Classical.choose (allHomes ⟨i.val + 1, by omega⟩)
  have resultFacts (i : Fin 4) := Classical.choose_spec (allHomes ⟨i.val + 1, by omega⟩)
  have resultSlots (i : Fin 4) : slots[15 + i.val]? = some (.bytes .word64 (results i)) := by
    have found := (resultFacts i).1
    change slots[14 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  have ordered (i : Fin 4) : carryHome.allocation < (results i).allocation :=
    homes.ordered 14 (15 + i.val) .word64 .word64 carryHome (results i) (by omega) carryLocal (resultSlots i)
  refine ⟨results, currentCall, ?_, carrySlot, ?_, carryWrite, ?_, carryRead, by simp [scalarCarryValue],
    ?_, (fun i => Ne.symm (Nat.ne_of_lt (ordered i))), ?_, carryFresh, ?_, preserved.cells, ?_⟩
  · intro reference member
    exact call.input_bytes_of_memory_below preserved member
  · intro i
    have found := (resultFacts i).2.1
    change frame.locals[15 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  · intro i
    exact (resultFacts i).2.2.2
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old : reference.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old carryFresh),
      fun i => Nat.ne_of_lt (Nat.lt_of_lt_of_le old (resultFacts i).2.2.1)⟩
  · intro i j different
    have distinct : i.val ≠ j.val := fun equal => different (Fin.ext equal)
    by_cases before : i.val < j.val
    · exact Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots i) (resultSlots j))
    · exact Ne.symm (Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots j) (resultSlots i)))
  · intro i
    exact (resultFacts i).2.2.1
  · intro index value impossible
    simp [UInt256Proof.AddSubtract.Safety.completedLocals] at impossible

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.CarrySafety

/-- From pc 162, zero the carry and run all four checked carry calls on the initial limbs. -/
theorem vector128_sse_repair_carry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (carry storage : Nat) (code : CodeAt body 162 (sseRepairCode carry storage))
    (carryFound : program[carry]? = some (carryBody body.profile))
    (wordSpecs : ∀ i : Fin 5, specs[14 + i.val]? = some armWordSpec)
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
    (continuation : ∀ carryHome results after,
      ScalarCarryState (program := program) original after frame left right output carryHome results 4 15 16 →
      ∃ fuel final returned,
        run program fuel method 193 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 162 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply ripple_start program body method specs found carry storage 162 14 code
    (wordSpecs 0) original.nextIdentity entered current [left, right] [output]
    frame root slots layout args currentCall enteredWF homes authority post
  intro carryHome after carrySlot carryRead retained afterCall afterAuthority _written
  obtain ⟨results, ready⟩ := vector128_sse_carry_ready program specs wordSpecs original entered after frame root slots layout
    left right output carryHome call afterCall (preserved.trans retained) homes enteredWF afterAuthority carrySlot carryRead
  exact vector128_sse_carry_all program body method found carry storage code carryFound
    ready args leftArg rightArg post (continuation carryHome results)

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- Store the four ripple words through the checked limb helper and return the exact carry. -/
theorem vector128_sse_finish (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (carry storage : Nat) (code : CodeAt body 162 (sseRepairCode carry storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (returns : body.returnsValue = true)
    (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarCarryState (program := program) original current frame left right output carryHome results 4 15 16) :
    ∃ fuel final values,
      run program fuel method 193 args frame [] current = .ok (final, values) ∧
      AddResult original final values left right output := by
  let words := scalarSumWord original left right
  let post := fun final values => AddResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply ripple_store_prefix program body method found carry storage 162 14 code
    output args outputArg frame current words formed state.snapshots post
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract body.profile program storage storageFound
      current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) 198 args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3)) [] current) := by
    simp [step, cil_guard, observerCount, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  obtain ⟨carryAllocation, carryPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.flagWrite
  have carryOld := (state.call.1.1.1 _ _ carryPresent).1
  have distinct : carryHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.flagFresh))
  have carryRead := authority.read_eq state.flagRead carryOld
    (fun i _ => outside _ _ (Or.inl distinct))
  have returned : run program 5 method 199 args frame [] stored =
      .ok (leaveFrame frame stored, [.scalar (.i32 (scalarOverflowFlag _))]) :=
    ripple_return program body method found carry storage 162 14 code returns
      args frame stored carryHome _ state.flagSlot carryRead
  obtain ⟨fuel, executed⟩ := run_call_exists found
    (by (conv => lhs; arg 2; whnf); cil_lookup [code]) stepped ⟨childFuel, invoked⟩ ⟨5, returned⟩
  refine ⟨fuel, leaveFrame frame stored, _, executed, ?_⟩
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity owned
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have computed : inputValue (leaveFrame frame stored) output = scalarSumValue original left right := by
      simpa only [inputValue, bytes, scalarSumValue] using value
    exact computed.trans (scalar_sum_value original left right)
  · rw [scalar_flag_overflow]
  · exact (retained.access output outputOld 32 1 true).trans
      (valid.1.writable (wordView output) (by simp))
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

end UInt256Proof.Add.Safety
