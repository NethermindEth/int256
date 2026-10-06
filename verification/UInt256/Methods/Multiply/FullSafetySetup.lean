import UInt256.Safety.InputLocalSafety
import UInt256.Methods.Multiply.BothTwoSafetySetup

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def fullIndex : Nat := Extracted.program.findIdx fun body =>
  body.localKinds == (List.replicate 22 CIL.LocalKind.word64 ++ List.replicate 4 CIL.LocalKind.vector256)

def fullBody : CIL.Method := Extracted.program[fullIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem full_frame_setup (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame fullBody (productArgs left right output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity fullBody.localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords Extracted.program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : fullBody.localKinds = (List.replicate 22 CIL.LocalKind.word64 ++ List.replicate 4 CIL.LocalKind.vector256) := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup fullBody
    (by rfl) (by simp [kinds]) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def fullInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original left 0)) 1 (inputLimb original right 0))
    2 (inputLimb original left 1)) 3 (inputLimb original right 1))
    4 (inputLimb original left 2)) 5 (inputLimb original right 2)

def fullTop (original : Memory) (left right : Reference) :=
  ((inputLimb original left 0 * inputLimb original right 3 + inputLimb original left 1 * inputLimb original right 2) +
    inputLimb original left 2 * inputLimb original right 1) + inputLimb original left 3 * inputLimb original right 0

theorem full_inputs (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullInputs original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 18 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  apply run_input_to_local (argument := 0) (target := 0) state originalCall enteredWF homes left (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m0 state0
  apply run_input_to_local (argument := 1) (target := 1) state0 originalCall enteredWF homes right (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m1 state1
  apply run_input_to_local (argument := 0) (target := 2) state1 originalCall enteredWF homes left (by simp) 1
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m2 state2
  apply run_input_to_local (argument := 1) (target := 3) state2 originalCall enteredWF homes right (by simp) 1
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m3 state3
  apply run_input_to_local (argument := 0) (target := 4) state3 originalCall enteredWF homes left (by simp) 2
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro m4 state4
  apply run_input_to_local (argument := 1) (target := 5) state4 originalCall enteredWF homes right (by simp) 2
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  exact continuation

#print axioms full_frame_setup
#print axioms full_inputs
end UInt256Proof.Multiply.Safety
