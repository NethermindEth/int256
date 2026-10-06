import UInt256.Methods.Add.VectorParentSetup
import CIL.Safety.CallComposition

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def prepareCall : Nat := prepareParentBody.code.findIdx fun op => match op with
  | .call callee 7 => callee == vectorIndex
  | _ => false

/-- Follow the parent's actual ISA guard and local-address instructions, then
    compose the checked helper invocation with its remaining execution. -/
theorem vector_parent_prepare_call (memory : Memory)
    (left right output sum mask incoming propagation : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output, sum, mask, incoming, propagation])
    (separate : PrepareSeparation output sum mask incoming propagation)
    (sumSlot : frame.locals[0]? = some (.bytes .vector256 sum))
    (maskSlot : frame.locals[1]? = some (.bytes .vector256 mask))
    (incomingSlot : frame.locals[2]? = some (.bytes .vector256 incoming))
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagation))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ReturnedState Extracted.program after [] →
      PrepareResult after output sum mask incoming propagation (inputValue memory left) (inputValue memory right) →
      (∀ id offset, id < memory.nextIdentity →
        (∀ reference ∈ [output, sum, mask, incoming, propagation], OutsideOutput reference id offset) →
        after.cells id offset = memory.cells id offset) →
      ∃ fuel final returned,
        run Extracted.program fuel prepareParentIndex (prepareCall + 1)
          (binaryArguments left right output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex 0 (binaryArguments left right output) frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨childFuel, after, certificate, result, footprint⟩ :=
    checked_prepare_contract memory left right output sum mask incoming propagation call separate
  have returnedState : ReturnedState Extracted.program after [] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, returned⟩ := certificate.2
    exact returned
  obtain ⟨tailFuel, final, returned, tail, satisfied⟩ := continuation after returnedState result footprint
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have fetched : prepareParentBody.code[prepareCall]? = some (.call vectorIndex 7) := by rfl
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have fs := call.output_formed (reference := sum) (by simp)
  have fm := call.output_formed (reference := mask) (by simp)
  have fi := call.output_formed (reference := incoming) (by simp)
  have fp := call.output_formed (reference := propagation) (by simp)
  have stepped : step prepareParentBody (.call vectorIndex 7) prepareCall
      (binaryArguments left right output) frame
      (prepareArguments left right output sum mask incoming propagation).reverse memory =
      .ok (.call vectorIndex (prepareArguments left right output sum mask incoming propagation) [] memory) := by
    simp [step, prepareArguments, checkedValue, formValue, fl, fr, fo, fs, fm, fi, fp,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨combined, executed⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩ ⟨tailFuel, tail⟩
  have done : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex prepareCall (binaryArguments left right output) frame
        (prepareArguments left right output sum mask incoming propagation).reverse memory =
          .ok (final, returned) ∧ post final returned := ⟨combined, final, returned, executed, satisfied⟩
  have profile : prepareParentBody.profile = Extracted.profile := by rfl
  conv at done in prepareCall => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, binaryArguments, prepareArguments, sumSlot, maskSlot, incomingSlot, propagationSlot,
           localAddress, checkedValue, formValue, fl, fr, fo, fs, fm, fi, fp,
           pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, numericValue,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector_parent_prepare_call
end UInt256Proof.Add.Safety
