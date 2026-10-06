import UInt256.Methods.Add.VectorSafetyContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def prepareParentIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with
    | .call callee 7 => callee == vectorIndex
    | _ => false

def prepareParentBody : CIL.Method := Extracted.program[prepareParentIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def prepareParentSpecs : List NumericLocalSpec := numericSpecs prepareParentBody

/-- The actual parent's fresh numeric homes discharge the helper's separation
    and writable-output obligations. The public caller needs no extra separation. -/
theorem prepare_parent_context (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ frame entered sum mask incoming propagation,
      enterFrame prepareParentBody (binaryArguments left right output) memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity prepareParentSpecs frame.locals ∧
      frame.locals[0]? = some (.bytes .vector256 sum) ∧
      frame.locals[1]? = some (.bytes .vector256 mask) ∧
      frame.locals[2]? = some (.bytes .vector256 incoming) ∧
      frame.locals[3]? = some (.bytes .vector256 propagation) ∧
      CallingConditions Extracted.program entered [left, right] [output, sum, mask, incoming, propagation] ∧
      PrepareSeparation output sum mask incoming propagation := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ := numeric_frame_setup prepareParentBody prepareParentSpecs
    (by rfl) (by rfl) (by rfl) memory (binaryArguments left right output) call.1.1
  obtain ⟨sum, sumSlot, sumBound, _, sumWritable⟩ := homes.home_at 0 vectorZeroSpec (by rfl)
  obtain ⟨mask, maskSlot, maskBound, _, maskWritable⟩ := homes.home_at 1 vectorZeroSpec (by rfl)
  obtain ⟨incoming, incomingSlot, incomingBound, _, incomingWritable⟩ := homes.home_at 2 vectorZeroSpec (by rfl)
  obtain ⟨propagation, propagationSlot, propagationBound, _, propagationWritable⟩ := homes.home_at 3 vectorZeroSpec (by rfl)
  have enteredCall := call.after_frame_setup setup
  have expandedCall : CallingConditions Extracted.program entered [left, right]
      [output, sum, mask, incoming, propagation] := by
    refine ⟨⟨enteredCall.1.1, enteredCall.1.2.1, ?_⟩, enteredCall.2⟩
    intro view member
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact enteredCall.1.2.2 (wordView output) (by simp)
    · exact sumWritable
    · exact maskWritable
    · exact incomingWritable
    · exact propagationWritable
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed (reference := output) (by simp))
  have old : output.allocation < memory.nextIdentity := (call.1.1.1 _ _ present).1
  refine ⟨frame, entered, sum, mask, incoming, propagation, setup, homes,
    sumSlot, maskSlot, incomingSlot, propagationSlot, expandedCall, ?_⟩
  exact ⟨Nat.ne_of_lt (homes.ordered 0 1 _ _ sum mask (by decide) sumSlot maskSlot),
    Nat.ne_of_lt (homes.ordered 0 2 _ _ sum incoming (by decide) sumSlot incomingSlot),
    Nat.ne_of_lt (homes.ordered 1 2 _ _ mask incoming (by decide) maskSlot incomingSlot),
    Nat.ne_of_gt (Nat.lt_of_lt_of_le old sumBound),
    Nat.ne_of_gt (Nat.lt_of_lt_of_le old maskBound),
    Nat.ne_of_gt (Nat.lt_of_lt_of_le old incomingBound),
    Nat.ne_of_lt (homes.ordered 0 3 _ _ sum propagation (by decide) sumSlot propagationSlot),
    Nat.ne_of_lt (homes.ordered 1 3 _ _ mask propagation (by decide) maskSlot propagationSlot),
    Nat.ne_of_lt (homes.ordered 2 3 _ _ incoming propagation (by decide) incomingSlot propagationSlot),
    Nat.ne_of_lt (Nat.lt_of_lt_of_le old propagationBound)⟩

#print axioms prepare_parent_context
end UInt256Proof.Add.Safety

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
