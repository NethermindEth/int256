import UInt256.Methods.Multiply.LeftTwoSafetyArithmetic
import UInt256.Methods.Multiply.StorageSafety
import UInt256.Methods.Multiply.BothTwoSafetyOutput

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem left_two_output (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (leftTwoFinalWords original left right))
    (leftUpper : inputLimb original left 2 = 0 ∧ inputLimb original left 3 = 0) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 95 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let known := leftTwoFinalWords original left right
  let words := leftTwoResultWords original left right
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have load (index : Nat) (value : BitVec 64) (present : known index = some value) (pc : Nat) (stack : List Value) :=
    state.snapshots.load (body := leftTwoBody) (args := productArgs left right output)
      (pc := pc) (stack := stack) (index := index) value present
  change ∃ fuel final returned, _ ∧ post final returned
  apply run_next_exists post found (by rfl)
  · simp [step, productArgs, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (load 6 (words 0) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 10 (words 1) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 13 (words 2) (by rfl) _ _)
  apply run_next_exists post found (by rfl) (load 4 (words 3) (by rfl) _ _)
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step leftTwoBody (.call productStoreIndex 5) 100 (productArgs left right output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] current =
      .ok (.call productStoreIndex [.reference (.address output), .scalar (.i64 (words 0)),
        .scalar (.i64 (words 1)), .scalar (.i64 (words 2)), .scalar (.i64 (words 3))] [] current) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run Extracted.program 1 leftTwoIndex 101 (productArgs left right output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : leftTwoBody.code[101]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original current result [left, right]
    output _ frame originalCall valid owned state.caller
    (packed.trans (left_two_words_correct original left right leftUpper)) readable outside⟩

#print axioms left_two_output
end UInt256Proof.Multiply.Safety
