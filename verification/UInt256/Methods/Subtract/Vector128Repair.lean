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
    state.flagSlot (by simpa [Nat.add_comm] using state.resultSlots index) rfl (fun _ => rfl)
    ⟨state.call.1.1, state.flagBound, state.flagRead, state.flagWrite, state.resultWrites index,
      Or.inl (Ne.symm (state.flagSeparate index))⟩ state.flagWrite (state.resultWrites index) post
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
  obtain ⟨results, ready⟩ := RippleState.initial program specs 10 wordSpecs
    original entered after frame root slots layout left right output borrowHome
    (scalarBorrowValue original left right) _ (by simp [scalarBorrowValue])
    call afterCall (preserved.trans retained) homes enteredWF afterAuthority borrowSlot borrowRead
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
  apply WP.exists_execution
  apply ripple_finish program body method found borrow storage 77 10 code
    storageFound returns original current frame left right output borrowHome results
    _ words args outputArg call state post
  intro stored valid outside value
  obtain ⟨_, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity owned
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have computed : inputValue (leaveFrame frame stored) output = scalarDifferenceValue original left right := by
      simpa only [inputValue, bytes, scalarDifferenceValue, UInt256Model.value] using value
    exact computed.trans (scalar_difference_value original left right)
  · exact congrArg (fun flag => [Value.scalar (.i32 flag)])
      (scalar_flag_underflow original left right)
  · exact (retained.access output outputOld 32 1 true).trans
      (valid.1.writable (wordView output) (by simp))
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

end UInt256Proof.Subtract.Profile
