import UInt256.Methods.Multiply.EntrySetup
import UInt256.Safety.OutputCallReturn

/-! The multiplication entry point dispatches on the saved zero masks to the single-word,
    scalar, two-limb and full paths; every branch returns the checked product. -/

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls
open UInt256Proof.Multiply.BothTwo (run_widen_locals run_product_storage)

private theorem product_padding (lo hi : BitVec 64) :
    BitVec.ofNat 256 (lo.toNat + hi.toNat * 2^64 + (0 : BitVec 64).toNat * 2^128 +
      (0 : BitVec 64).toNat * 2^192) = BitVec.ofNat 256 (lo.toNat + hi.toNat * 2^64) := by
  simp (config := { implicitDefEqProofs := false }) only
    [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem multiply_left_two_branch (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word) (swapped : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (upper : inputUpper original (if swapped then right else left) = 0) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry (if swapped then 78 else 71)
        (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let firstInput := if swapped then right else left
  let secondInput := if swapped then left else right
  have firstMember : firstInput ∈ [left, right] := by cases swapped <;> simp [firstInput]
  have secondMember : secondInput ∈ [left, right] := by cases swapped <;> simp [secondInput]
  have call : CallingConditions ctx.program current [firstInput, secondInput] [output] := by
    cases swapped
    · exact state.call
    · refine ⟨⟨state.call.1.1, ?_, state.call.1.writable⟩, state.call.2⟩
      intro view member
      apply state.call.1.readable view
      simpa [firstInput, secondInput, or_comm] using member
  have zero : inputLimb current firstInput 2 = 0 ∧ inputLimb current firstInput 3 = 0 := by
    simpa only [state.input_limb originalCall firstInput firstMember] using
      input_upper_zero original firstInput upper
  obtain ⟨childFuel, childFinal, invoked, result⟩ := LeftTwo.left_two_invoke_with_storage ctx.profile ctx.program ctx.indices.leftTwo ctx.indices.word ctx.indices.count ctx.indices.storage ctx.storage ctx.leftTwo ctx.count word current firstInput secondInput output call zero
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    have firstValue := state.input_value originalCall firstInput firstMember
    have secondValue := state.input_value originalCall secondInput secondMember
    change OutputResult current childFinal output
      (inputValue current firstInput * inputValue current secondInput) [] at result
    rw [firstValue, secondValue] at result
    cases swapped
    · exact result
    · simpa only [firstInput, secondInput, ite_true, BitVec.mul_comm] using result
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  cases swapped <;> dsimp [firstInput, secondInput] at invoked ⊢
  all_goals
    cil_contract_steps 3 [productArgs, leftFormed, rightFormed, outputFormed]
    exact run_output_call (callee := ctx.indices.leftTwo) state originalCall owned _ found (by rfl)
      (by cil_checked_step [productArgs, leftFormed, rightFormed, outputFormed])
      (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩

theorem multiply_scalar_branch (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word) (swapped : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (small : inputTail original (if swapped then left else right) = 0) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry (if swapped then 55 else 48)
        (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let firstInput := if swapped then right else left
  let secondInput := if swapped then left else right
  have firstMember : firstInput ∈ [left, right] := by cases swapped <;> simp [firstInput]
  have secondMember : secondInput ∈ [left, right] := by cases swapped <;> simp [secondInput]
  let smallWord := inputLimb original secondInput 0
  have call : CallingConditions ctx.program current [firstInput] [output] := by
    refine ⟨⟨state.call.1.1, ?_, state.call.1.writable⟩, state.call.2⟩
    intro view member
    apply state.call.1.readable view
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
    subst view
    exact List.mem_map.mpr ⟨firstInput, firstMember, rfl⟩
  obtain ⟨childFuel, childFinal, invoked, result⟩ := ScalarSafety.scalar_invoke_with_storage ctx.profile ctx.program ctx.indices.single ctx.indices.word ctx.indices.storage ctx.storage ctx.single word current firstInput output smallWord call
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    have firstValue := state.input_value originalCall firstInput firstMember
    have smallValue := input_tail_single original secondInput small
    refine ⟨result.returns, result.wellFormed, ?_, result.writable, result.readable, result.footprint⟩
    rw [result.value, firstValue, ← smallValue]
    cases swapped
    · rfl
    · exact BitVec.mul_comm _ _
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  cases swapped <;> dsimp [firstInput, secondInput, smallWord] at invoked ⊢
  all_goals
    cil_contract_steps (snapshots := state.snapshots.toLocalSnapshots)
      [productArgs, leftFormed, rightFormed, outputFormed, multiplyInputs]
    exact run_output_call (callee := ctx.indices.single) state originalCall owned _ found (by rfl)
      (by cil_checked_step [ScalarSafety.scalarArgs, leftFormed, rightFormed, outputFormed])
      (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩

theorem multiply_invoke (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage) (memory : Memory) (left right output : Reference)
    (call : CallingConditions ctx.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke ctx.program fuel ctx.indices.entry (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, initial⟩ :=
    multiply_frame_setup ctx memory left right output call
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) :=
    ctx.entry
  have body : ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply multiply_prepare ctx memory entered entered left right output frame call enteredWF homes
      initial post
    intro current state
    have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
    have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
    have outputFormed := state.call.output_formed (by simp : output ∈ [output])
    have expected {childFinal : Memory}
        (result : ProductResult current childFinal left right output []) :
        OutputResult current childFinal output
          (inputValue memory left * inputValue memory right) [] := by
      simpa only [BothTwo.ProductResult, state.input_value call left (by simp),
        state.input_value call right (by simp)] using result
    have words := state.snapshots.toLocalSnapshots
    cil_contract_steps (snapshots := words) [multiplyInputs]
    by_cases small : inputTail memory left ||| inputTail memory right = 0#64
    · simp only [small]
      have halves := BitVec.or_eq_zero_iff.mp small
      apply WP.exists_execution
      apply run_widen_locals word state call enteredWF homes 0 1 7 6
        (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
      intro _ next
      cil_contract_steps (snapshots := next.snapshots.toLocalSnapshots)
        [productArgs, next.call.output_formed (by simp : output ∈ [output])]
      apply WP.exists_execution
      exact run_product_storage ctx.storage next call owned
        (fun index => if index.val = 0 then lowProduct (inputLimb memory left 0)
            (inputLimb memory right 0)
          else if index.val = 1 then highProduct (inputLimb memory left 0)
            (inputLimb memory right 0) else 0)
        ((product_padding _ _).trans (small_product_value memory left right halves.1 halves.2))
        found (by rfl) (by rfl)
    simp only [small, not_false_eq_true, ↓reduceIte]
    cil_contract_steps (snapshots := words) [multiplyInputs]
    by_cases rightSmall : inputTail memory right = 0#64
    · simp only [rightSmall]
      exact multiply_scalar_branch ctx word false memory entered current left right output frame
        call owned state rightSmall
    simp only [rightSmall, not_false_eq_true, ↓reduceIte]
    cil_contract_steps (snapshots := words) [multiplyInputs]
    by_cases leftSmall : inputTail memory left = 0#64
    · simp only [leftSmall]
      exact multiply_scalar_branch ctx word true memory entered current left right output frame
        call owned state leftSmall
    simp only [leftSmall, not_false_eq_true, ↓reduceIte]
    cil_contract_steps (snapshots := words) [multiplyInputs]
    by_cases bothTwo : inputUpper memory left ||| inputUpper memory right = 0#64
    · simp only [bothTwo]
      have halves := BitVec.or_eq_zero_iff.mp bothTwo
      cil_contract_steps 3 [productArgs, leftFormed, rightFormed, outputFormed]
      obtain ⟨childFuel, childFinal, invoked, result⟩ := BothTwo.both_two_invoke_with_storage
        ctx.profile ctx.program ctx.indices.bothTwo ctx.indices.word ctx.indices.count
        ctx.indices.storage ctx.storage ctx.bothTwo ctx.count word current left right output
        state.call
        (by simpa only [state.input_limb call left (by simp)] using
          input_upper_zero memory left halves.1)
        (by simpa only [state.input_limb call right (by simp)] using
          input_upper_zero memory right halves.2)
      exact run_output_call (callee := ctx.indices.bothTwo) state call owned _ found (by rfl)
        (by cil_checked_step [productArgs, leftFormed, rightFormed, outputFormed])
        (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected result⟩
    simp only [bothTwo, not_false_eq_true, ↓reduceIte]
    cil_contract_steps (snapshots := words) [multiplyInputs]
    by_cases leftTwo : inputUpper memory left = 0#64
    · simp only [leftTwo]
      exact multiply_left_two_branch ctx word false memory entered current left right output
        frame call owned state leftTwo
    simp only [leftTwo, not_false_eq_true, ↓reduceIte]
    cil_contract_steps (snapshots := words) [multiplyInputs]
    by_cases rightTwo : inputUpper memory right = 0#64
    · simp only [rightTwo]
      exact multiply_left_two_branch ctx word true memory entered current left right output
        frame call owned state rightTwo
    simp only [rightTwo, not_false_eq_true, ↓reduceIte]
    cil_contract_steps 3 [productArgs, leftFormed, rightFormed, outputFormed]
    obtain ⟨childFuel, childFinal, invoked, result⟩ := Full.full_invoke_with_storage ctx.profile
      ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage
      ctx.storage ctx.full ctx.count word top current left right output state.call
    exact run_output_call (callee := ctx.indices.full) state call owned _ found (by rfl)
      (by cil_checked_step [productArgs, leftFormed, rightFormed, outputFormed])
      (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected result⟩
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns := result.returns
  subst returned
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  exact invoke_of_run found checked setup ran

end UInt256Proof.Multiply.Entry
