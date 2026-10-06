import Extracted
import UInt256.Safety.ReadOnlyForwarder
import CIL.Safety.StepComposition
import UInt256.Safety.ArgumentValues
import UInt256.Safety.CallerSetup
import UInt256.Safety.ReadOnlyValueContract

namespace UInt256Proof.ValueSafety

open CIL.Safety UInt256Model.Safety

/-- Setup creates the actual address-taken argument home from the passed value. -/
theorem value_setup (memory : Memory) (left : Reference) (right : BitVec 256)
    (call : CallingConditions Extracted.program memory [left] []) :
    ∃ frame entered copy,
      enterFrame Extracted.entryBody (valueArguments left right) memory = .ok (frame, entered) ∧
      argumentHome frame 1 = .ok (.bytes .vector256 copy) ∧
      CallingConditions Extracted.program entered [left, copy] [] ∧
      inputValue entered copy = right ∧
      inputValue entered left = inputValue memory left := by
  obtain ⟨copy, entered, made, loaded, _, _⟩ :=
    make_argument_home256 memory memory.nextIdentity 1 (valueArguments left right) right call.1.1 rfl
  let frame : Frame := {
    activation := memory.nextIdentity, locals := [], owned := [copy.allocation],
    arguments := [(1, .bytes .vector256 copy)] }
  have setup : enterFrame Extracted.entryBody (valueArguments left right) memory = .ok (frame, entered) := by
    simp [enterFrame, cil_code, makeLocals, made, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨frame, entered, copy, setup, ?_,
    (call.after_frame_setup setup).with_readable_input loaded,
    inputValue_of_encoded_read loaded, call.input_value_after_setup setup (by simp)⟩
  simp [argumentHome, frame, Pure.pure, Except.pure]

#print axioms value_setup



def valueCall : Nat := Extracted.entryBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

theorem value_prefix (memory : Memory) (left copy : Reference) (right : BitVec 256)
    (frame : Frame)
    (home : argumentHome frame 1 = .ok (.bytes .vector256 copy))
    (call : CallingConditions Extracted.program memory [left, copy] [])
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex valueCall (valueArguments left right) frame
        [.reference (.address copy), .reference (.address left)] memory = .ok (final, values) ∧
      post final values) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex 0 (valueArguments left right) frame [] memory =
        .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fc := call.input_formed (reference := copy) (by simp)
  conv at continuation in valueCall => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [step, valueArguments, home, localAddress, checkedValue, formValue, fl, fc,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem value_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : Memory) :
    run Extracted.program 1 Extracted.entryIndex (valueCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  conv in valueCall => cbv
  simp only [Nat.reduceAdd]
  simp [run, cil_code, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms value_prefix
#print axioms value_return


theorem value_entry_checked (callee : Nat) (operation : BitVec 256 → BitVec 256 → BitVec 32)
    (fetched : Extracted.entryBody.code[valueCall]? = some (.call callee 2))
    (child : BinaryReadOnlyInvocation (fun x y => .i32 (operation x y)) Extracted.program callee)
    (memory : Memory) (left : Reference) (right : BitVec 256)
    (call : CallingConditions Extracted.program memory [left] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program Extracted.entryIndex (valueArguments left right) memory fuel final
        [.scalar (.i32 (operation (inputValue memory left) right))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, copy, setup, home, enteredCall, copyValue, leftValue⟩ :=
    value_setup memory left right call
  have lookup : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have checked : (valueArguments left right).mapM (checkedValue memory) =
      .ok (valueArguments left right) := by
    have formed := call.input_formed (reference := left) (by simp)
    simp [valueArguments, checkedValue, formValue, numericValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ := child entered left copy enteredCall
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fc := enteredCall.input_formed (reference := copy) (by simp)
  have stepped : step Extracted.entryBody (.call callee 2) valueCall
      (valueArguments left right) frame [.reference (.address copy), .reference (.address left)] entered =
      .ok (.call callee (readOnlyArguments [left, copy]) [] entered) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fc, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, childCertificate.1⟩ ⟨1, value_return _ _ frame childFinal⟩
  let flag : BitVec 32 := operation (inputValue entered left) (inputValue entered copy)
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame childFinal ∧ values = [.scalar (.i32 flag)]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    value_prefix entered left copy right frame home enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have initialFlag : flag = (operation (inputValue memory left) right) := by
    simp only [flag, leftValue, copyValue]
  rw [initialFlag] at finished
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame childFinal memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((childCells id (Nat.lt_of_lt_of_le bound fresh.1.next) offset).trans (before.cells id bound offset))

#print axioms value_entry_checked


end UInt256Proof.ValueSafety
