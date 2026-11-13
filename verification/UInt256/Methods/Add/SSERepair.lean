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
  obtain ⟨results, ready⟩ := RippleState.initial program (numericKinds specs) 14 1
    original entered after frame slots (by simp only [layout, List.getElem?_cons_succ, implies_true])
    (fun i => (homes.home_at _ _ (wordSpecs i)).imp (fun _ facts => facts.1)) left right output carryHome
    (scalarCarryValue original left right) _ (by simp [scalarCarryValue])
    call afterCall (preserved.trans retained) homes.writable enteredWF afterAuthority carrySlot carryRead
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
  apply WP.exists_execution
  apply ripple_finish program body method found carry storage 162 14 code
    storageFound returns original current frame left right output carryHome results
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
  · have computed : inputValue (leaveFrame frame stored) output = scalarSumValue original left right := by
      simpa only [inputValue, bytes, scalarSumValue, UInt256Model.value] using value
    exact computed.trans (scalar_sum_value original left right)
  · exact congrArg (fun flag => [Value.scalar (.i32 flag)])
      (scalar_flag_overflow original left right)
  · exact (retained.access output outputOld 32 1 true).trans
      (valid.1.writable (wordView output) (by simp))
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

end UInt256Proof.Add.Safety
