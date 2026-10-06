import UInt256.Methods.Add.VectorSafetyContract

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
