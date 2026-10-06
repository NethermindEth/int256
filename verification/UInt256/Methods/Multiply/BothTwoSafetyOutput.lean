import UInt256.Methods.Multiply.BothTwoSafetyArithmetic
import UInt256.Methods.Multiply.StorageSafety
import UInt256.Safety.OutputReturn

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def ProductResult (original final : Memory) (left right output : Reference) (returned : List Value) :=
  OutputResult original final output (inputValue original left * inputValue original right) returned

theorem both_two_output (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (bothTwoFinalWords original left right))
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0)
    (rightUpper : inputLimb original right 2 = 0 ∧ inputLimb original right 3 = 0) :
    ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 63 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let known := bothTwoFinalWords original left right
  let words := bothTwoResultWords original left right
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have load (index : Nat) (value : BitVec 64) (present : known index = some value) (pc : Nat) (stack : List Value) :=
    state.snapshots.load (body := bothTwoBody) (args := productArgs left right output)
      (pc := pc) (stack := stack) (index := index) value present
  change ∃ fuel final returned, _ ∧ post final returned
  apply run_next_exists post found (by rfl)
  · simp [step, productArgs, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (load 4 (words 0) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 8 (words 1) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 11 (words 2) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 12 (localWord known 12) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 7 (localWord known 7) (by rfl) _ _)
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step bothTwoBody (.call productStoreIndex 5) 70 (productArgs left right output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] current =
      .ok (.call productStoreIndex [.reference (.address output), .scalar (.i64 (words 0)),
        .scalar (.i64 (words 1)), .scalar (.i64 (words 2)), .scalar (.i64 (words 3))] [] current) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run Extracted.program 1 bothTwoIndex 71 (productArgs left right output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : bothTwoBody.code[71]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original current result [left, right]
    output _ frame originalCall valid owned state.caller
    (packed.trans (both_two_words_correct original left right leftUpper rightUpper)) readable outside⟩

#print axioms both_two_output
end UInt256Proof.Multiply.Safety
