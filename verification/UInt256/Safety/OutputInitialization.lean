import UInt256.Safety.OutputAccess
import CIL.Safety.StepComposition

namespace UInt256Model.Safety
open CIL.Safety

/-- A checked initialization prefix. SkipInit only validates the reference;
    the subsequent scalar store establishes initialization of the selected limb. -/
theorem output_initialization_prefix (program : CIL.Program) (method pc argument : Nat)
    (body : CIL.Method) (frame : Frame) (args : List Value) (memory : Memory)
    (inputs outputs : List Reference) (output : Reference) (index : Fin 4)
    (call : CallingConditions program memory inputs outputs) (member : output ∈ outputs)
    (found : program[method]? = some body)
    (arg : args[argument]? = some (.reference (.address output)))
    (code : ∀ i : Fin 8, body.code[pc + i.val]? =
      ([.arg argument, .skipInit, .arg argument, .fieldAddr index, .asRef,
        .const32 0, .convI8, .store64] : List CIL.Op)[i.val]?)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory { output with offset := output.offset + 8 * index.val } (numberBytes 0 8) 1 = .ok after →
      CallingConditions program after inputs outputs →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = memory.cells id offset) →
      ∃ fuel final returned, run program fuel method (pc + 8) args frame [] after = .ok (final, returned) ∧
        post final returned) :
    ∃ fuel final returned, run program fuel method pc args frame [] memory = .ok (final, returned) ∧
      post final returned := by
  obtain ⟨after, written, valid, outside, _⟩ := call.write_output_slice member (8 * index.val)
    (numberBytes 0 8) (by simp [numberBytes]) (by simp [numberBytes]; omega)
  have formed := call.output_formed member
  have limbFormed := call.output_limb_formed member index
  have address := call.output_limb_address member index
  have done := continuation after written valid outside
  have h0 := code ⟨0, by decide⟩
  have h1 := code ⟨1, by decide⟩
  have h2 := code ⟨2, by decide⟩
  have h3 := code ⟨3, by decide⟩
  have h4 := code ⟨4, by decide⟩
  have h5 := code ⟨5, by decide⟩
  have h6 := code ⟨6, by decide⟩
  have h7 := code ⟨7, by decide⟩

  iterate 8
    apply run_next_exists post found (by first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7)
    simp [step, arg, checkedValue, numericValue, pureArity, scalars, CIL.step,
      instruction, formValue, formed, limbFormed, address, storeValue, referenceAt, written,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact done

#print axioms output_initialization_prefix
end UInt256Model.Safety
