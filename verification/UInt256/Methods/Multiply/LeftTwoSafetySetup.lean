import UInt256.Safety.InputLocalSafety
import UInt256.Methods.Multiply.BothTwoSafetySetup

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def leftTwoIndex : Nat := Extracted.program.findIdx fun body =>
  body.localKinds == List.replicate 18 CIL.LocalKind.word64

def leftTwoBody : CIL.Method := Extracted.program[leftTwoIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem left_two_frame_setup (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame leftTwoBody (productArgs left right output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity leftTwoBody.localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords Extracted.program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : leftTwoBody.localKinds = List.replicate 18 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup leftTwoBody
    (by rfl) (by simp [kinds]) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def leftTwoInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original left 1)) 1 (inputLimb original right 0))
    2 (inputLimb original right 1)) 3 (inputLimb original right 2)

theorem left_two_inputs (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity leftTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (leftTwoInputs original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel leftTwoIndex 14 (productArgs left right output) frame
          [.scalar (.i64 (inputLimb original left 0))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel leftTwoIndex 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[leftTwoIndex]? = some leftTwoBody := by rfl
  have formed := state.call.input_formed (by simp : left ∈ [left, right])
  have reading := state.input_field originalCall left (by simp) 0
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, productArgs, checkedValue, formValue, formed, reading, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_input_to_local (argument := 0) (target := 0) state originalCall enteredWF homes left (by simp) 1
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m0 state0
  apply run_input_to_local (argument := 1) (target := 1) state0 originalCall enteredWF homes right (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m1 state1
  apply run_input_to_local (argument := 1) (target := 2) state1 originalCall enteredWF homes right (by simp) 1
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m2 state2
  apply run_input_to_local (argument := 1) (target := 3) state2 originalCall enteredWF homes right (by simp) 2
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  exact continuation

#print axioms left_two_frame_setup
#print axioms left_two_inputs
end UInt256Proof.Multiply.Safety
