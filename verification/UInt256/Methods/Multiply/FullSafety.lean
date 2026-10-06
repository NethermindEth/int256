import UInt256.Methods.Multiply.FullSafetyMiddle
import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ZeroProducts
import UInt256.Safety.HalfRepresentation
import UInt256.Methods.Multiply.StorageSafety
import UInt256.Methods.Multiply.BothTwoSafetyOutput
import UInt256.Methods.Multiply.FullSafetyTopContract

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullFirstUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullMiddleWords original left right) 0 5 17 16) 15 17 13 15
  rememberWord known 6 (localWord known 6 + localWord known 16)

theorem full_first_upper (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullMiddleWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullFirstUpperWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 153 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 139 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let k0 := fullMiddleWords original left right
  apply run_local_word_call state originalCall enteredWF homes 0 5 17 16
    (localWord k0 0) (localWord k0 5) (lowProduct (localWord k0 0) (localWord k0 5))
    (highProduct (localWord k0 0) (localWord k0 5))
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 0 5 17 16
  apply run_local_word_call state1 originalCall enteredWF homes 15 17 13 15
    (localWord k1 15) (localWord k1 17) (countCarry (localWord k1 15) (localWord k1 17) (localWord k1 13))
    (localWord k1 15 + localWord k1 17)
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
  intro m2 state2
  let k2 := countWords k1 15 17 13 15
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 16) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
    (localWord k2 6 + localWord k2 16) 152 (productArgs left right output) [] (body := fullBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms full_first_upper

def fullUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullFirstUpperWords original left right) 2 3 19 18) 15 19 13 15
  rememberWord known 6 (localWord known 6 + localWord known 18)

theorem full_upper (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullFirstUpperWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullUpperWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 167 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 153 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let k0 := fullFirstUpperWords original left right
  apply run_local_word_call state originalCall enteredWF homes 2 3 19 18
    (localWord k0 2) (localWord k0 3) (lowProduct (localWord k0 2) (localWord k0 3))
    (highProduct (localWord k0 2) (localWord k0 3))
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 2 3 19 18
  apply run_local_word_call state1 originalCall enteredWF homes 15 19 13 15
    (localWord k1 15) (localWord k1 19) (countCarry (localWord k1 15) (localWord k1 19) (localWord k1 13))
    (localWord k1 15 + localWord k1 19)
    (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
  intro m2 state2
  let k2 := countWords k1 15 19 13 15
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 18) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
    (localWord k2 6 + localWord k2 18) 166 (productArgs left right output) [] (body := fullBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms full_upper

end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullFinalWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullUpperWords original left right) 4 1 21 20) 15 21 13 15
  rememberWord known 6 (localWord known 6 + (localWord known 20 + localWord known 13))

theorem full_final (contract : WordContract)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullUpperWords original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullFinalWords original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 183 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 167 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  let k0 := fullUpperWords original left right
  apply run_local_word_call state originalCall enteredWF homes 4 1 21 20
    (localWord k0 4) (localWord k0 1) (lowProduct (localWord k0 4) (localWord k0 1))
    (highProduct (localWord k0 4) (localWord k0 1)) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
  intro m1 state1
  let k1 := widenWords k0 4 1 21 20
  apply run_local_word_call state1 originalCall enteredWF homes 15 21 13 15
    (localWord k1 15) (localWord k1 21) (countCarry (localWord k1 15) (localWord k1 21) (localWord k1 13))
    (localWord k1 15 + localWord k1 21) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
    found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (counting_local_effect state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
  intro m2 state2
  let k2 := countWords k1 15 21 13 15
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 20) (localWord_known _ _ (by rfl)))
  apply run_next_exists post found (by rfl) (state2.snapshots.load (localWord k2 13) (localWord_known _ _ (by rfl)))
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, scalars, numericValue, CIL.step, CIL.binary,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
    (localWord k2 6 + (localWord k2 20 + localWord k2 13)) 182 (productArgs left right output) [] (body := fullBody)
  exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms full_final
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullResultWords (original : Memory) (left right : Reference) : UInt256Model.Limbs := fun index =>
  let known := fullFinalWords original left right
  localWord known (if index.val = 0 then 8 else if index.val = 1 then 14 else if index.val = 2 then 15 else 6)

theorem full_words_correct (original : Memory) (left right : Reference) :
    UInt256Model.value (fullResultWords original left right) = inputValue original left * inputValue original right := by
  have words : fullResultWords original left right = productLimbs (inputLimb original left) (inputLimb original right) := by
    funext ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [fullResultWords, fullFinalWords, fullUpperWords, fullFirstUpperWords, fullMiddleWords,
        fullSecondColumn, fullFirstProducts, fullPrepared, fullInputs, fullTop,
        localWord, widenWords, countWords, rememberWord,
        productLimbs, firstColumn, secondColumn, topWords, column, columnStep,
        countCarry, lowProduct, BitVec.add_assoc]
  rw [words, product_limbs_correct, input_limbs_value, input_limbs_value]

#print axioms full_words_correct
end UInt256Proof.Multiply.Safety

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

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem full_invoke (contract : WordContract) (top : FullTopContract) (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel fullIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := full_frame_setup memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have body : ∃ fuel final returned,
      run Extracted.program fuel fullIndex 0 (productArgs left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply full_inputs memory entered entered left right output frame call enteredWF homes state post
    intro m0 state0
    apply top memory entered m0 left right output frame call enteredWF homes state0 post
    intro m1 state1
    apply full_second_column contract memory entered m1 left right output frame call enteredWF homes state1 post
    intro m2 state2
    apply full_middle_column memory entered m2 left right output frame call enteredWF homes state2 post
    intro m3 state3
    apply full_first_upper contract memory entered m3 left right output frame call enteredWF homes state3 post
    intro m4 state4
    apply full_upper contract memory entered m4 left right output frame call enteredWF homes state4 post
    intro m5 state5
    apply full_final contract memory entered m5 left right output frame call enteredWF homes state5 post
    intro m6 state6
    exact full_output memory entered m6 left right output frame call owned state6
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns := result.returns
  subst returned
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

#print axioms full_invoke
end UInt256Proof.Multiply.Safety
