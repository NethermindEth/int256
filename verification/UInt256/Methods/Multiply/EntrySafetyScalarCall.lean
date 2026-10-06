import UInt256.Methods.Multiply.EntrySafetyArithmetic
import UInt256.Methods.Multiply.ScalarSafety
import UInt256.Methods.Multiply.BothTwoSafetyOutput
import UInt256.Safety.OutputCallReturn
import UInt256.Safety.ReadOnlyForwarder

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
