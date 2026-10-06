import UInt256.Methods.Add.VectorSafetyPropagation
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Finish the preparation helper, preserving its caller's private snapshots
    across the public output write and retiring only the helper's own frame. -/
theorem vector_prepare_finish (original entered current : Memory)
    (inputs outputs : List Reference) (output sum incoming propagation : Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (outputMember : output ∈ outputs) (sumMember : sum ∈ outputs)
    (incomingMember : incoming ∈ outputs) (propagationMember : propagation ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (sumOutput : sum.allocation ≠ output.allocation)
    (outputPropagation : output.allocation ≠ propagation.allocation)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (incomingArgument : args[5]? = some (.reference (.address incoming)))
    (propagationArgument : args[6]? = some (.reference (.address propagation)))
    (sumValue incomingValue : BitVec 256)
    (sumRead : read current sum 32 1 = .ok (numberBytes sumValue.toNat 32))
    (incomingRead : read current incoming 32 1 = .ok (numberBytes incomingValue.toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current = .ok (final, []) ∧
      read final output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· - ·) sumValue incomingValue).toNat 32) ∧
      read final propagation 32 1 = .ok (numberBytes (propagationMask sumValue).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      access final propagation 32 1 true = .ok () ∧
      (∀ reference width alignment bytes, reference.allocation < original.nextIdentity →
        reference.allocation ≠ output.allocation → reference.allocation ≠ propagation.allocation →
        read current reference width alignment = .ok bytes → read final reference width alignment = .ok bytes) ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset → OutsideOutput propagation id offset →
        final.cells id offset = current.cells id offset) := by
  have old : ∀ reference ∈ outputs, reference.allocation < original.nextIdentity := by
    intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
    exact (call.1.1.1 _ _ present).1
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [] ∧
    read final output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· - ·) sumValue incomingValue).toNat 32) ∧
    read final propagation 32 1 = .ok (numberBytes (propagationMask sumValue).toNat 32) ∧
    access final output 32 1 true = .ok () ∧ access final propagation 32 1 true = .ok () ∧
    (∀ reference width alignment bytes, reference.allocation < original.nextIdentity →
      reference.allocation ≠ output.allocation → reference.allocation ≠ propagation.allocation →
      read current reference width alignment = .ok bytes → read final reference width alignment = .ok bytes) ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset → OutsideOutput propagation id offset →
      final.cells id offset = current.cells id offset)
  have finished : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_early_output_checked original entered current inputs outputs output sum incoming frame args call currentCall
      outputMember sumMember incomingMember authority outputArgument sumArgument incomingArgument
      sumValue incomingValue sumRead incomingRead post
    intro middle outputWrite outputRead middleCall middleAuthority outputOutside _ _
    have retainedSum := write_preserves_disjoint_read outputWrite sumRead (Or.inl sumOutput)
    apply vector_propagation_checked original entered middle inputs outputs sum propagation frame args call middleCall
      sumMember propagationMember middleAuthority sumArgument propagationArgument sumValue retainedSum post
    intro after propagationWrite propagationRead afterCall _ propagationOutside _ _
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨1, leaveFrame frame after, [], vector_prepare_return after frame args, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (teardown.read output (old output outputMember) 32 1).trans
        (write_preserves_disjoint_read propagationWrite outputRead (Or.inl outputPropagation))
    · exact (teardown.read propagation (old propagation propagationMember) 32 1).trans propagationRead
    · exact (teardown.access output (old output outputMember) 32 1 true).trans
        (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, outputMember, rfl⟩))
    · exact (teardown.access propagation (old propagation propagationMember) 32 1 true).trans
        (afterCall.1.2.2 (wordView propagation) (List.mem_map.mpr ⟨propagation, propagationMember, rfl⟩))
    · intro reference width alignment bytes older notOutput notPropagation loaded
      exact (teardown.read reference older width alignment).trans
        (write_preserves_disjoint_read propagationWrite
          (write_preserves_disjoint_read outputWrite loaded (Or.inl notOutput)) (Or.inl notPropagation))
    · intro id offset older notOutput notPropagation
      exact (teardown.cells id older offset).trans
        ((propagationOutside id offset notPropagation).trans (outputOutside id offset notOutput))
  obtain ⟨fuel, final, returned, executed, result, rest⟩ := finished
  subst returned
  exact ⟨fuel, final, executed, rest⟩

#print axioms vector_prepare_finish
end UInt256Proof.Add.Safety
