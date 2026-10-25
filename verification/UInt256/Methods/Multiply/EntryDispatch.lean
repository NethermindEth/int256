import UInt256.Methods.Multiply.EntrySetup
import UInt256.Safety.OutputCallReturn

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

private theorem product_padding (lo hi : BitVec 64) :
    BitVec.ofNat 256 (lo.toNat + hi.toNat * 2^64 + (0 : BitVec 64).toNat * 2^128 +
      (0 : BitVec 64).toNat * 2^192) = BitVec.ofNat 256 (lo.toNat + hi.toNat * 2^64) := by
  simp (config := { implicitDefEqProofs := false }) only
    [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem multiply_small_branch (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (leftSmall : inputTail original left = 0) (rightSmall : inputTail original right = 0) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 32 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let a := inputLimb original left 0
  let b := inputLimb original right 0
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  apply run_local_word_call state originalCall enteredWF homes 0 1 7 6
    a b (lowProduct a b) (highProduct a b) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect word current a b state.call.1.1 reference ready) post
  intro after next
  have formed := next.call.output_formed (by simp : output ∈ [output])
  have loadLow := fun (pc : Nat) (stack : List Value) => next.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 7) (lowProduct a b) (by rfl)
  have loadHigh := fun (pc : Nat) (stack : List Value) => next.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 6) (highProduct a b) (by rfl)
  iterate 7
    apply run_next_exists post found (by rfl)
    first
    | exact loadLow _ _
    | exact loadHigh _ _
    | simp [step, cil_guard, observerCount, productArgs, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def,
        formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, childFinal, invoked, valid, outside, _, value, readable⟩ :=
    ctx.storage after [left, right] output (lowProduct a b) (highProduct a b) 0 0 next.call
  have expected : OutputResult after childFinal output (inputValue original left * inputValue original right) [] := by
    refine ⟨rfl, valid.1.1, ?_, valid.1.2.2 (wordView output) (by simp), readable, ?_⟩
    · exact value.trans ((product_padding _ _).trans
        (small_product_value original left right leftSmall rightSmall))
    · exact fun id _ offset beyond => outside id offset beyond
  apply run_output_call (callee := ctx.indices.storage)
    next originalCall owned (inputValue original left * inputValue original right)
    found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
  simp [step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  try rfl

#print axioms multiply_small_branch
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

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
    · refine ⟨⟨state.call.1.1, ?_, state.call.1.2.2⟩, state.call.2⟩
      intro view member
      apply state.call.1.2.1 view
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
    iterate 3
      apply run_next_exists post found (by rfl)
      simp [step, cil_guard, observerCount, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_output_call (callee := ctx.indices.leftTwo)
      state originalCall owned (inputValue original left * inputValue original right)
      found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
    simp [step, cil_guard, observerCount, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

#print axioms multiply_left_two_branch
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem multiply_both_two_branch (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (leftUpper : inputUpper original left = 0) (rightUpper : inputUpper original right = 0) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 64 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 3
    apply run_next_exists post found (by rfl)
    simp [step, cil_guard, observerCount, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  have leftZero : inputLimb current left 2 = 0 ∧ inputLimb current left 3 = 0 := by
    simpa only [state.input_limb originalCall left (by simp)] using input_upper_zero original left leftUpper
  have rightZero : inputLimb current right 2 = 0 ∧ inputLimb current right 3 = 0 := by
    simpa only [state.input_limb originalCall right (by simp)] using input_upper_zero original right rightUpper
  obtain ⟨childFuel, childFinal, invoked, result⟩ := BothTwo.both_two_invoke_with_storage ctx.profile ctx.program ctx.indices.bothTwo ctx.indices.word ctx.indices.count ctx.indices.storage ctx.storage ctx.bothTwo ctx.count word current left right output state.call leftZero rightZero
  have leftValue := state.input_value originalCall left (by simp)
  have rightValue := state.input_value originalCall right (by simp)
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    change OutputResult current childFinal output (inputValue current left * inputValue current right) [] at result
    rw [leftValue, rightValue] at result
    exact result
  apply run_output_call (callee := ctx.indices.bothTwo) (callArgs := productArgs left right output)
    state originalCall owned (inputValue original left * inputValue original right)
    found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
  simp [step, cil_guard, observerCount, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  try rfl

#print axioms multiply_both_two_branch
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem multiply_full_branch (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame
      (multiplyInputs original left right)) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 83 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have leftFormed := state.call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := state.call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := state.call.output_formed (by simp : output ∈ [output])
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 3
    apply run_next_exists post found (by rfl)
    simp [step, cil_guard, observerCount, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, childFinal, invoked, result⟩ := Full.full_invoke_with_storage ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage ctx.storage ctx.full ctx.count word top current left right output state.call
  have leftValue := state.input_value originalCall left (by simp)
  have rightValue := state.input_value originalCall right (by simp)
  have expected : OutputResult current childFinal output (inputValue original left * inputValue original right) [] := by
    change OutputResult current childFinal output (inputValue current left * inputValue current right) [] at result
    rw [leftValue, rightValue] at result
    exact result
  apply run_output_call (callee := ctx.indices.full) (callArgs := productArgs left right output)
    state originalCall owned (inputValue original left * inputValue original right)
    found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
  simp [step, cil_guard, observerCount, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  try rfl

#print axioms multiply_full_branch
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem multiply_large_dispatch (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame
      (multiplyInputs original left right)) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 60 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have loadLeft := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 2) (inputUpper original left) (by rfl)
  have loadRight := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 3) (inputUpper original right) (by rfl)
  apply run_next_exists post found (by rfl) (loadLeft _ _)
  apply run_next_exists post found (by rfl) (loadRight _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, cil_guard, observerCount, pureArity, numericValue, scalars, CIL.step.eq_def, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
  by_cases both : inputUpper original left ||| inputUpper original right = 0
  · simp only [both, ite_true]
    have halves := BitVec.or_eq_zero_iff.mp both
    exact multiply_both_two_branch ctx word original entered current left right output frame originalCall owned state halves.1 halves.2
  · simp only [both, ite_false]
    apply run_next_exists post found (by rfl) (loadLeft _ _)
    apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
    by_cases leftZero : inputUpper original left = 0
    · simp only [leftZero, ite_true]
      exact multiply_left_two_branch ctx word false original entered current left right output frame originalCall owned state leftZero
    · simp only [leftZero, ite_false]
      apply run_next_exists post found (by rfl) (loadRight _ _)
      apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
      by_cases rightZero : inputUpper original right = 0
      · simp only [rightZero, ite_true]
        exact multiply_left_two_branch ctx word true original entered current left right output frame originalCall owned state rightZero
      · simp only [rightZero, ite_false]
        exact multiply_full_branch ctx word top original entered current left right output frame originalCall owned state

#print axioms multiply_large_dispatch
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

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
    refine ⟨⟨state.call.1.1, ?_, state.call.1.2.2⟩, state.call.2⟩
    intro view member
    apply state.call.1.2.1 view
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
  have loadWord := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := if swapped then 0 else 1) smallWord (by cases swapped <;> rfl)
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
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
      | simp [step, cil_guard, observerCount, productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_output_call (callee := ctx.indices.single)
      state originalCall owned (inputValue original left * inputValue original right)
      found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
    simp [step, cil_guard, observerCount, ScalarSafety.scalarArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

#print axioms multiply_scalar_branch
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem multiply_dispatch (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame
      (multiplyInputs original left right)) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 28 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let post := fun final returned => ProductResult original final left right output returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have loadLeft := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 4) (inputTail original left) (by rfl)
  have loadRight := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 5) (inputTail original right) (by rfl)
  apply run_next_exists post found (by rfl) (loadLeft _ _)
  apply run_next_exists post found (by rfl) (loadRight _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, cil_guard, observerCount, pureArity, numericValue, scalars, CIL.step.eq_def, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
  by_cases both : inputTail original left ||| inputTail original right = 0
  · simp only [both, ite_true]
    have halves := BitVec.or_eq_zero_iff.mp both
    exact multiply_small_branch ctx word original entered current left right output frame originalCall enteredWF homes owned state halves.1 halves.2
  · simp only [both, ite_false]
    apply run_next_exists post found (by rfl) (loadRight _ _)
    apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
    by_cases rightZero : inputTail original right = 0
    · simp only [rightZero, ite_true]
      exact multiply_scalar_branch ctx word false original entered current left right output frame originalCall owned state rightZero
    · simp only [rightZero, ite_false]
      apply run_next_exists post found (by rfl) (loadLeft _ _)
      apply run_next_exists post found (by rfl) (step_word_nonzero _ _ _ _ _ _ _)
      by_cases leftZero : inputTail original left = 0
      · simp only [leftZero, ite_true]
        exact multiply_scalar_branch ctx word true original entered current left right output frame originalCall owned state leftZero
      · simp only [leftZero, ite_false]
        exact multiply_large_dispatch ctx word top original entered current left right output frame originalCall owned state

#print axioms multiply_dispatch
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem multiply_invoke (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word) (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage) (memory : Memory) (left right output : Reference)
    (call : CallingConditions ctx.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke ctx.program fuel ctx.indices.entry (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := multiply_frame_setup ctx memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply multiply_prepare ctx memory entered entered left right output frame call enteredWF homes state post
    intro current prepared
    exact multiply_dispatch ctx word top memory entered current left right output frame call enteredWF homes owned prepared
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns := result.returns
  subst returned
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  exact invoke_of_run found checked setup ran

#print axioms multiply_invoke
end UInt256Proof.Multiply.Entry



