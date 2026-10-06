import UInt256.Methods.Add.VectorReportingCascade
import UInt256.Methods.Add.VectorReportingFast

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model

theorem vector_reporting_branches (original entered current : Memory)
    (left right output sum mask incoming propagation : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame prepareParentBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity prepareParentSpecs frame.locals)
    (state : ReturnedState Extracted.program current [])
    (sumSlot : frame.locals[0]? = some (.bytes .vector256 sum))
    (maskSlot : frame.locals[1]? = some (.bytes .vector256 mask))
    (incomingSlot : frame.locals[2]? = some (.bytes .vector256 incoming))
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagation))
    (a b : Limbs)
    (prepared : PrepareResult current output sum mask incoming propagation (value a) (value b)) :
    ∃ fuel final,
      run Extracted.program fuel prepareParentIndex (prepareCall+1)
        (binaryArguments left right output) frame [] current = .ok (final, [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  by_cases fast : (propagationMask (CIL.Vector.zip256 (· + ·) (value a) (value b))) &&&
      (incomingCarry (generatedCarry (value a) (value b))) = BitVec.ofNat 256 0
  · obtain ⟨fuel, final, executed, result, writable, preserved⟩ := vector_reporting_fast
      original entered current left right output sum mask incoming propagation frame call setup
      maskSlot incomingSlot propagationSlot a b prepared fast
    exact ⟨fuel, final, executed, result, writable, fun id offset old _ => preserved.cells id old offset⟩
  · let post : Memory → List Value → Prop := fun final returned =>
      returned = [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))] ∧ read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset
    have finish : ∃ fuel final returned,
        run Extracted.program fuel prepareParentIndex (prepareCall+1)
          (binaryArguments left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
      apply vector_reporting_branch current frame (binaryArguments left right output) propagation incoming _ _
        propagationSlot incomingSlot prepared.propagationRead prepared.incomingRead post
      simp only [fast, ite_false]
      obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_reporting_cascade
        original entered current left right output sum mask incoming propagation frame call setup homes state
        sumSlot maskSlot propagationSlot a b prepared
      exact ⟨fuel, final, _, executed, rfl, result, writable, footprint⟩
    obtain ⟨fuel, final, returned, executed, same, result, writable, footprint⟩ := finish
    subst returned
    exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_reporting_branches
end UInt256Proof.Add.Safety
