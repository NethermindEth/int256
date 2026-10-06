import UInt256.Methods.Multiply.EntrySafetyArithmetic
import UInt256.Methods.Multiply.ScalarSafety
import UInt256.Methods.Multiply.BothTwoSafetyOutput
import UInt256.Safety.OutputCallReturn
import UInt256.Safety.ReadOnlyForwarder
import UInt256.Methods.Multiply.EntrySafetyLargeDispatch
import UInt256.Methods.Multiply.EntrySafetySmall
import CIL.Safety.ScalarBranch

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_scalar_branch (word : WordContract) (swapped : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (small : inputTail original (if swapped then left else right) = 0) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex (if swapped then 55 else 48)
        (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let firstInput := if swapped then right else left
  let secondInput := if swapped then left else right
  have firstMember : firstInput ∈ [left, right] := by cases swapped <;> simp [firstInput]
  have secondMember : secondInput ∈ [left, right] := by cases swapped <;> simp [secondInput]
  let smallWord := inputLimb original secondInput 0
  have call : CallingConditions Extracted.program current [firstInput] [output] := by
    refine ⟨⟨state.call.1.1, ?_, state.call.1.2.2⟩, state.call.2⟩
    intro view member
    apply state.call.1.2.1 view
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
    subst view
    exact List.mem_map.mpr ⟨firstInput, firstMember, rfl⟩
  obtain ⟨childFuel, childFinal, invoked, result⟩ := scalar_invoke word current firstInput output smallWord call
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    have firstValue := state.input_value originalCall firstInput firstMember
    have smallValue := input_tail_single original secondInput small
    refine ⟨result.returns, result.wellFormed, ?_, result.writable, result.readable, result.footprint⟩
    rw [result.value, firstValue, ← smallValue]
    cases swapped
    · rfl
    · exact BitVec.mul_comm _ _
  have loadWord := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := if swapped then 0 else 1) smallWord (by cases swapped <;> rfl)
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  cases swapped <;> dsimp [firstInput, secondInput, smallWord] at invoked loadWord ⊢
  all_goals
    iterate 3
      apply run_next_exists post found (by rfl)
      first
      | exact loadWord _ _
      | simp [step, productArgs, scalarArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_output_call (callee := scalarIndex)
      state originalCall owned (inputValue original left * inputValue original right)
      found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
    simp [step, productArgs, scalarArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

#print axioms multiply_scalar_branch
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_dispatch (word : WordContract) (top : FullTopContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right)) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 28 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have loadLeft := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 4) (inputTail original left) (by rfl)
  have loadRight := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 5) (inputTail original right) (by rfl)
  apply run_next_exists post found (by rfl) (loadLeft _ _)
  apply run_next_exists post found (by rfl) (loadRight _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, numericValue, scalars, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
  by_cases both : inputTail original left ||| inputTail original right = 0
  · simp only [both, ite_true]
    have halves := BitVec.or_eq_zero_iff.mp both
    exact multiply_small_branch word original entered current left right output frame originalCall enteredWF homes owned state halves.1 halves.2
  · simp only [both, ite_false]
    apply run_next_exists post found (by rfl) (loadRight _ _)
    apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
    by_cases rightZero : inputTail original right = 0
    · simp only [rightZero, ite_true]
      exact multiply_scalar_branch word false original entered current left right output frame originalCall owned state rightZero
    · simp only [rightZero, ite_false]
      apply run_next_exists post found (by rfl) (loadLeft _ _)
      apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
      by_cases leftZero : inputTail original left = 0
      · simp only [leftZero, ite_true]
        exact multiply_scalar_branch word true original entered current left right output frame originalCall owned state leftZero
      · simp only [leftZero, ite_false]
        exact multiply_large_dispatch word top original entered current left right output frame originalCall owned state

#print axioms multiply_dispatch
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem multiply_invoke (word : WordContract) (top : FullTopContract) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel multiplyIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := multiply_frame_setup memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply multiply_prepare memory entered entered left right output frame call enteredWF homes state post
    intro current prepared
    exact multiply_dispatch word top memory entered current left right output frame call enteredWF homes owned prepared
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns := result.returns
  subst returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

#print axioms multiply_invoke
end UInt256Proof.Multiply.Safety
