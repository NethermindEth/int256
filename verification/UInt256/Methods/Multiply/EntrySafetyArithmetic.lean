import UInt256.Safety.InputLocalSafety
import UInt256.Methods.Multiply.BothTwoSafetySetup
import UInt256.Methods.Multiply.SingleWord
import UInt256.Safety.HalfRepresentation
import UInt256.Safety.PrivateInputValues

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def multiplyIndex : Nat := Extracted.program.findIdx fun body =>
  body.localKinds == List.replicate 8 CIL.LocalKind.word64

def multiplyBody : CIL.Method := Extracted.program[multiplyIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem multiply_frame_setup (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame multiplyBody (productArgs left right output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity multiplyBody.localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords Extracted.program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : multiplyBody.localKinds = List.replicate 8 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup multiplyBody
    (by rfl) (by simp [kinds]) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def multiplyLowInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (fun _ => none) 0 (inputLimb original left 0)) 1 (inputLimb original right 0)

theorem multiply_low_inputs (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (multiplyLowInputs original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel multiplyIndex 6 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  apply run_input_to_local (argument := 0) (target := 0) state originalCall enteredWF homes left (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro after afterState
  apply run_input_to_local (argument := 1) (target := 1) afterState originalCall enteredWF homes right (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  exact continuation

#print axioms multiply_frame_setup
#print axioms multiply_low_inputs
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def inputUpper (memory : Memory) (input : Reference) :=
  inputLimb memory input 2 ||| inputLimb memory input 3

theorem multiply_upper_mask (rightSide : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame known)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord known (if rightSide then 3 else 2) (inputUpper original (if rightSide then right else left))) →
      ∃ fuel final returned,
        run Extracted.program fuel multiplyIndex (if rightSide then 18 else 12)
          (productArgs left right output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex (if rightSide then 12 else 6)
        (productArgs left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
  let input := if rightSide then right else left
  let pc := if rightSide then 12 else 6
  let index := if rightSide then 3 else 2
  have member : input ∈ [left, right] := by cases rightSide <;> simp [input]
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have formed := state.call.input_formed member
  have reading2 := state.input_field originalCall input member 2
  have reading3 := state.input_field originalCall input member 3
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes index (by cases rightSide <;> rfl)
    (inputUpper original input) (pc + 5) (productArgs left right output) [] (body := multiplyBody)
  cases rightSide <;> dsimp [input, pc, index] at formed reading2 reading3 stored next continuation ⊢
  all_goals
    iterate 5
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, pureArity, productArgs, checkedValue, numericValue, formValue, formed, reading2, reading3,
          checkedAt, scalars, CIL.step, CIL.binary, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored (continuation after next)

def inputTail (memory : Memory) (input : Reference) :=
  inputLimb memory input 1 ||| inputUpper memory input

theorem multiply_tail_mask (rightSide : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame known)
    (knownUpper : known (if rightSide then 3 else 2) = some (inputUpper original (if rightSide then right else left)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord known (if rightSide then 5 else 4) (inputTail original (if rightSide then right else left))) →
      ∃ fuel final returned,
        run Extracted.program fuel multiplyIndex (if rightSide then 28 else 23)
          (productArgs left right output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex (if rightSide then 23 else 18)
        (productArgs left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
  let input := if rightSide then right else left
  let pc := if rightSide then 23 else 18
  let index := if rightSide then 5 else 4
  have member : input ∈ [left, right] := by cases rightSide <;> simp [input]
  have found : Extracted.program[multiplyIndex]? = some multiplyBody := by rfl
  have formed := state.call.input_formed member
  have reading := state.input_field originalCall input member 1
  have loadUpper := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := multiplyBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    (inputUpper original input) knownUpper
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes index (by cases rightSide <;> rfl)
    (inputTail original input) (pc + 4) (productArgs left right output) [] (body := multiplyBody)
  cases rightSide <;> dsimp [input, pc, index] at formed reading loadUpper stored next continuation ⊢
  all_goals
    iterate 4
      apply run_next_exists post found (by rfl)
      first
      | exact loadUpper _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, pureArity, productArgs, checkedValue, numericValue, formValue, formed, reading,
            checkedAt, scalars, CIL.step, CIL.binary, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms multiply_upper_mask
#print axioms multiply_tail_mask
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def multiplyUpperInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (multiplyLowInputs original left right)
    2 (inputUpper original left)) 3 (inputUpper original right)

def multiplyInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (multiplyUpperInputs original left right)
    4 (inputTail original left)) 5 (inputTail original right)

theorem multiply_prepare (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity multiplyBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (multiplyInputs original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel multiplyIndex 28 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel multiplyIndex 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply multiply_low_inputs original entered current left right output frame originalCall enteredWF homes state post
  intro m0 state0
  apply multiply_upper_mask false original entered m0 left right output frame _ originalCall enteredWF homes state0 post
  intro m1 state1
  apply multiply_upper_mask true original entered m1 left right output frame _ originalCall enteredWF homes state1 post
  intro m2 state2
  apply multiply_tail_mask false original entered m2 left right output frame _ originalCall enteredWF homes state2 (by rfl) post
  intro m3 state3
  apply multiply_tail_mask true original entered m3 left right output frame _ originalCall enteredWF homes state3 (by rfl) post
  exact continuation

#print axioms multiply_prepare
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem input_upper_zero (memory : Memory) (input : Reference)
    (zero : inputUpper memory input = 0) :
    inputLimb memory input 2 = 0 ∧ inputLimb memory input 3 = 0 :=
  BitVec.or_eq_zero_iff.mp zero

theorem input_tail_single (memory : Memory) (input : Reference)
    (zero : inputTail memory input = 0) :
    inputValue memory input = BitVec.ofNat 256 (inputLimb memory input 0).toNat := by
  have limbs := singleWord_eq (inputLimb memory input) zero
  exact (input_limbs_value memory input).symm.trans
    ((congrArg UInt256Model.value limbs.symm).trans (singleWord_value (inputLimb memory input 0)))

theorem small_product_value (memory : Memory) (left right : Reference)
    (leftSmall : inputTail memory left = 0) (rightSmall : inputTail memory right = 0) :
    BitVec.ofNat 256 ((lowProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat +
      (highProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat * 2^64) =
      inputValue memory left * inputValue memory right := by
  rw [input_tail_single memory left leftSmall, input_tail_single memory right rightSmall]
  rw [← BitVec.ofNat_mul]
  apply congrArg (BitVec.ofNat 256)
  rw [Nat.mul_comm (highProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat]
  exact product_decomposition (inputLimb memory left 0) (inputLimb memory right 0)

#print axioms input_upper_zero
#print axioms input_tail_single
#print axioms small_product_value
end UInt256Proof.Multiply.Safety
