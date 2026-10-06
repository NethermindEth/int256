import UInt256.Methods.Multiply.FullSafetyArithmetic
import UInt256.Methods.Multiply.StorageSafety
import UInt256.Methods.Multiply.BothTwoSafetyOutput

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem full_output (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullFinalWords original left right)) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 183 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ ProductResult original final left right output returned := by
  let known := fullFinalWords original left right
  let words := fullResultWords original left right
  let post := fun final returned => ProductResult original final left right output returned
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have load (index : Nat) (value : BitVec 64) (present : known index = some value) (pc : Nat) (stack : List Value) :=
    state.snapshots.load (body := fullBody) (args := productArgs left right output)
      (pc := pc) (stack := stack) (index := index) value present
  change ∃ fuel final returned, _ ∧ post final returned
  apply run_next_exists post found (by rfl)
  · simp [step, productArgs, checkedValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (load 8 (words 0) (localWord_known _ _ (by rfl)) _ _)
  apply run_next_exists post found (by rfl) (load 14 (words 1) (localWord_known _ _ (by rfl)) _ _)
  apply run_next_exists post found (by rfl) (load 15 (words 2) (localWord_known _ _ (by rfl)) _ _)
  apply run_next_exists post found (by rfl) (load 6 (words 3) (localWord_known _ _ (by rfl)) _ _)
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step fullBody (.call productStoreIndex 5) 188 (productArgs left right output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] current =
      .ok (.call productStoreIndex [.reference (.address output), .scalar (.i64 (words 0)),
        .scalar (.i64 (words 1)), .scalar (.i64 (words 2)), .scalar (.i64 (words 3))] [] current) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run Extracted.program 1 fullIndex 189 (productArgs left right output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : fullBody.code[189]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, output_result_of_storage original current result [left, right]
    output _ frame originalCall valid owned state.caller
    (packed.trans (full_words_correct original left right)) readable outside⟩

#print axioms full_output
end UInt256Proof.Multiply.Safety
