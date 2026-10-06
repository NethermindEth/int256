import Extracted
import UInt256.Safety.PrivateWords
import CIL.Safety.StepComposition

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

def scalarIndex : Nat := Extracted.program.findIdx fun body =>
  body.localKinds == List.replicate 9 CIL.LocalKind.word64

def scalarBody : CIL.Method := Extracted.program[scalarIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def scalarArgs (input : Reference) (word : BitVec 64) (output : Reference) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

theorem scalar_frame_setup (memory : Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ frame entered,
      enterFrame scalarBody (scalarArgs input word output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity scalarBody.localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords Extracted.program memory entered entered [input] [output] frame (fun _ => none) := by
  have kinds : scalarBody.localKinds = List.replicate 9 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup scalarBody
    (by rfl) (by simp [kinds]) (by rfl) memory (scalarArgs input word output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

/-- Each input limb is loaded from the original caller bytes before being
    written to a previously unknown private home. -/
theorem scalar_input_save (original entered current : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame) (known : Nat → Option (BitVec 64)) (index : Fin 3)
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity scalarBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame known)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [input] [output] frame
        (rememberWord known index.val (inputLimb original input ⟨index.val, by omega⟩)) →
      ∃ fuel final returned,
        run Extracted.program fuel scalarIndex (25 + 3 * index.val)
          (scalarArgs input word output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex (22 + 3 * index.val)
        (scalarArgs input word output) frame [] current = .ok (final, returned) ∧ post final returned := by
  have specified : scalarBody.localKinds[index.val]? = some .word64 := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl
  obtain ⟨after, stored, updated⟩ := state.store enteredWF homes index.val specified
    (inputLimb original input ⟨index.val, by omega⟩) (24 + 3 * index.val) (scalarArgs input word output) []
      (body := scalarBody)
  have done := continuation after updated
  have formed := state.call.input_formed (by simp : input ∈ [input])
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (originalCall.input_formed (by simp : input ∈ [input]))
  have old := (originalCall.1.1.1 _ _ present).1
  have bytes : (fun offset => (current.cells input.allocation offset).bits) =
      (fun offset => (original.cells input.allocation offset).bits) := by
    funext offset
    rw [state.caller input.allocation old offset]
  have reading (rest : List Value) :
      instruction (.field ⟨index.val, by omega⟩) (.reference (.address input) :: rest) current =
        .ok (current, .scalar (.i64 (inputLimb original input ⟨index.val, by omega⟩)) :: rest) := by
    rw [state.call.input_field_instruction (by simp : input ∈ [input])]
    simp only [inputLimb, bytes]
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp at reading stored done
    iterate 2
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, pureArity, scalarArgs, checkedValue, numericValue, formValue, formed, reading,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored done

#print axioms scalar_frame_setup
#print axioms scalar_input_save
end UInt256Proof.Multiply.Safety
