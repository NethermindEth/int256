import UInt256.Methods.Add.VectorReportingBranches
import UInt256.Safety.ReportingContract
import UInt256.RepresentationLemmas

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model

/-- Full checked vector parent contract, including both carry-propagation paths
    and arbitrary valid input/output overlap. -/
theorem checked_vector_reporting_contract : ReportingBinaryContract (· + ·)
    (fun a b => decide (2^256 ≤ a.toNat + b.toNat))
    Extracted.program prepareParentIndex := by
  intro memory left right output call
  obtain ⟨frame, entered, sum, mask, incoming, propagation, setup, homes,
      sumSlot, maskSlot, incomingSlot, propagationSlot, enteredCall, separate⟩ :=
    prepare_parent_context memory left right output call
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have advanced := (enterFrame_fresh _ _ _ _ _ setup).1.next
  have leftValue : value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (inputValue memory left + inputValue memory right).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = memory.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply vector_parent_prepare_call entered left right output sum mask incoming propagation frame enteredCall separate
      sumSlot maskSlot incomingSlot propagationSlot post
    intro current state prepared prefixFootprint
    rw [call.input_value_after_setup setup (by simp : left ∈ [left, right]),
        call.input_value_after_setup setup (by simp : right ∈ [left, right])] at prepared
    obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_reporting_branches
      memory entered current left right output sum mask incoming propagation frame call setup homes state
      sumSlot maskSlot incomingSlot propagationSlot (inputLimb memory left) (inputLimb memory right)
      (by simpa only [leftValue, rightValue] using prepared)
    simp only [leftValue, rightValue] at executed result
    refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
    intro id offset old outside
    have privateOutside (reference : Reference) (bound : memory.nextIdentity ≤ reference.allocation) :
        OutsideOutput reference id offset := Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le old bound))
    have allOutside : ∀ reference ∈ [output, sum, mask, incoming, propagation], OutsideOutput reference id offset := by
      intro reference member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      · exact outside
      · exact privateOutside _ (homes.home_bound 0 _ _ sumSlot)
      · exact privateOutside _ (homes.home_bound 1 _ _ maskSlot)
      · exact privateOutside _ (homes.home_bound 2 _ _ incomingSlot)
      · exact privateOutside _ (homes.home_bound 3 _ _ propagationSlot)
    exact (footprint id offset old outside).trans
      ((prefixFootprint id offset (Nat.lt_of_lt_of_le old advanced) allOutside).trans
        (preserved.cells id old offset))
  obtain ⟨fuel, final, returned, executed, same, result, writable, footprint⟩ := finish
  subst returned
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have certificate := certify_invocation Extracted.program prepareParentIndex prepareParentBody
    (binaryArguments left right output) memory frame entered fuel final _
    (by rfl) checked setup (call.binary_entry_live setup) executed
  refine ⟨fuel, final, ?_, ?_, writable, fun id old offset outside => footprint id offset old outside⟩
  · simpa only [decide_eq_true_eq] using certificate
  ·
    have decoded := congrArg CIL.Safety.byteNumber (read_result_snapshot result)
    rw [byteNumber_numberBytes,
      byteNumber_snapshot (fun offset => (final.cells output.allocation offset).bits) output.offset 32] at decoded
    have bound : (inputValue memory left + inputValue memory right).toNat < 256^32 :=
      (inputValue memory left + inputValue memory right).isLt
    rw [Nat.mod_eq_of_lt bound] at decoded
    change BitVec.ofNat 256
      (UInt256Model.byteNumber (fun offset => (final.cells output.allocation offset).bits) output.offset 32) = _
    rw [← decoded, BitVec.ofNat_toNat, BitVec.setWidth_eq]

#print axioms checked_vector_reporting_contract
end UInt256Proof.Add.Safety
