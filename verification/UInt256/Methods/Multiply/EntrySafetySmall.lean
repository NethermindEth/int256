import UInt256.Methods.Multiply.EntrySafetyArithmetic
import UInt256.Methods.Multiply.BothTwoSafetyOutput
import UInt256.Safety.OutputCallReturn

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

private theorem product_padding (lo hi : BitVec 64) :
    BitVec.ofNat 256 (lo.toNat + hi.toNat * 2^64 + (0 : BitVec 64).toNat * 2^128 +
      (0 : BitVec 64).toNat * 2^192) = BitVec.ofNat 256 (lo.toNat + hi.toNat * 2^64) := by
  simp (config := { implicitDefEqProofs := false }) only
    [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem multiply_small_branch (word : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (multiplyInputs original left right))
    (leftSmall : inputTail original left = 0) (rightSmall : inputTail original right = 0) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 32 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let a := inputLimb original left 0
  let b := inputLimb original right 0
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  apply run_local_word_call state originalCall enteredWF homes 0 1 7 6
    a b (lowProduct a b) (highProduct a b) (by rfl) (by rfl) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect word current a b state.call.1.1 reference ready) post
  intro after next
  have formed := next.call.output_formed (by simp : output ∈ [output])
  have loadLow := fun (pc : Nat) (stack : List Value) => next.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 7) (lowProduct a b) (by rfl)
  have loadHigh := fun (pc : Nat) (stack : List Value) => next.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (index := 6) (highProduct a b) (by rfl)
  iterate 7
    apply run_next_exists post found (by rfl)
    first
    | exact loadLow _ _
    | exact loadHigh _ _
    | simp [step, productArgs, checkedValue, numericValue, pureArity, scalars, CIL.step,
        formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, childFinal, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract after [left, right] output (lowProduct a b) (highProduct a b) 0 0 next.call
  have expected : OutputResult after childFinal output (inputValue original left * inputValue original right) [] := by
    refine ⟨rfl, valid.1.1, ?_, valid.1.2.2 (wordView output) (by simp), readable, ?_⟩
    · exact value.trans ((product_padding _ _).trans
        (small_product_value original left right leftSmall rightSmall))
    · exact fun id _ offset beyond => outside id offset beyond
  apply run_output_call (callee := productStoreIndex)
    next originalCall owned (inputValue original left * inputValue original right)
    found (by rfl) _ (by rfl) (by rfl) ⟨childFuel, childFinal, invoked, expected⟩
  simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

#print axioms multiply_small_branch
end UInt256Proof.Multiply.Safety
