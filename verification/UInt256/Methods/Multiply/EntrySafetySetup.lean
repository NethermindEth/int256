import UInt256.Safety.InputLocalSafety
import UInt256.Methods.Multiply.BothTwoSafetySetup

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
