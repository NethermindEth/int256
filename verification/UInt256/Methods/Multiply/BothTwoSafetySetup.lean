import UInt256.Safety.PrivateWordAccess
import UInt256.Methods.Multiply.WordCallSafety
import CIL.Safety.StepComposition

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def bothTwoIndex : Nat := Extracted.program.findIdx fun body =>
  body.localKinds == List.replicate 14 CIL.LocalKind.word64

def bothTwoBody : CIL.Method := Extracted.program[bothTwoIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def productArgs (left right output : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output)]

theorem both_two_frame_setup (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame bothTwoBody (productArgs left right output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity bothTwoBody.localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords Extracted.program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : bothTwoBody.localKinds = List.replicate 14 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup bothTwoBody
    (by rfl) (by simp [kinds]) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def bothTwoInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original right 0)) 1 (inputLimb original left 1)) 2 (inputLimb original right 1)

theorem both_two_inputs (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity bothTwoBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (bothTwoInputs original left right) →
      ∃ fuel final returned,
        run Extracted.program fuel bothTwoIndex 11 (productArgs left right output) frame
          [.scalar (.i64 (inputLimb original left 0))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel bothTwoIndex 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[bothTwoIndex]? = some bothTwoBody := by rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have formedRight := state.call.input_formed (by simp : right ∈ [left, right])
  have loadLeft := state.input_field originalCall left (by simp) 0
  have loadRight := state.input_field originalCall right (by simp) 0
  iterate 4
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, productArgs, checkedValue, formValue, formedLeft, formedRight,
      loadLeft, loadRight, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m0, store0, state0⟩ := state.store enteredWF homes 0 (by rfl) (inputLimb original right 0)
    4 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) store0
  have formedLeft := state0.call.input_formed (by simp : left ∈ [left, right])
  have loadLeft := state0.input_field originalCall left (by simp) 1
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, productArgs, checkedValue, formValue, formedLeft, loadLeft,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m1, store1, state1⟩ := state0.store enteredWF homes 1 (by rfl) (inputLimb original left 1)
    7 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := bothTwoBody)
  apply run_next_exists post found (by rfl) store1
  have formedRight := state1.call.input_formed (by simp : right ∈ [left, right])
  have loadRight := state1.input_field originalCall right (by simp) 1
  iterate 2
    apply run_next_exists post found (by rfl)
    simp [step, pureArity, productArgs, checkedValue, formValue, formedRight, loadRight,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨m2, store2, state2⟩ := state1.store enteredWF homes 2 (by rfl) (inputLimb original right 1)
    10 (productArgs left right output) [.scalar (.i64 (inputLimb original left 0))] (body := bothTwoBody)
  exact run_next_exists post found (by rfl) store2 (continuation m2 state2)

#print axioms both_two_frame_setup
#print axioms both_two_inputs
end UInt256Proof.Multiply.Safety
