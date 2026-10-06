import UInt256.Methods.Add.VectorParentBranch
import UInt256.Methods.Add.VectorParentFastMath

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model

/-- The parent's fast suffix returns the mathematical sum and retires only its
    private frame. Caller output remains initialized and writable. -/
theorem vector_parent_fast (original entered current : Memory)
    (left right output sum mask incoming propagation : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame prepareParentBody (binaryArguments left right output) original =
      .ok (frame, entered))
    (incomingSlot : frame.locals[2]? = some (.bytes .vector256 incoming))
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagation))
    (a b : Limbs)
    (prepared : PrepareResult current output sum mask incoming propagation (value a) (value b))
    (fast : parentPropagationBits
      (propagationMask (CIL.Vector.zip256 (· + ·) (value a) (value b)))
      (incomingCarry (generatedCarry (value a) (value b))) = BitVec.ofNat 32 0) :
    ∃ fuel final,
      run Extracted.program fuel prepareParentIndex (prepareCall + 1)
        (binaryArguments left right output) frame [] current = .ok (final, []) ∧
      read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      MemoryBelow original.nextIdentity current final := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [] ∧
    read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    MemoryBelow original.nextIdentity current final
  have finish : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex (prepareCall + 1)
        (binaryArguments left right output) frame [] current = .ok (final, returned) ∧
      post final returned := by
    apply vector_parent_branch current frame (binaryArguments left right output)
      propagation incoming _ _ propagationSlot incomingSlot
      prepared.propagationRead prepared.incomingRead post
    simp only [fast, ite_true]
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame current original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (reference := output) (by simp))
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    refine ⟨1, leaveFrame frame current, [], vector_parent_return _ _ _, rfl, ?_, ?_, teardown⟩
    · rw [teardown.read output old 32 1]
      have result := prepared.outputRead
      rw [vector_fast_sum a b fast] at result
      exact result
    · exact (teardown.access output old 32 1 true).trans prepared.outputWritable
  obtain ⟨fuel, final, returned, executed, same, result, writable, retained⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, retained⟩

#print axioms vector_parent_fast
end UInt256Proof.Add.Safety
