import UInt256.Methods.Add.VectorRepairLookupFinal

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- Complete the propagation branch from saved vector masks through checked
    index arithmetic, lookup, correction and return. -/
theorem repair_tail_execution (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame repairBody args original = .ok (frame, entered))
    (enteredWF : entered.WellFormed)
    (advanced : entered.nextIdentity ≤ current.nextIdentity)
    (homes : NumericHomes entered original.nextIdentity repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[3]? = some (.reference (.address output)))
    (sumValue generated propagation : BitVec 256)
    (sumArgument : args[0]? = some (.scalar (.v256 sumValue)))
    (generatedArgument : args[1]? = some (.scalar (.v256 generated)))
    (propagationArgument : args[2]? = some (.scalar (.v256 propagation))) :
    ∃ fuel final,
      run Extracted.program fuel repairIndex 2 args frame [] current =
        .ok (final, [.scalar (.i32 (if (moveMask64 propagation + 2 * moveMask64 generated) &&& 16 > 0 then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (zip256 (· + ·) sumValue (cascadeVector (cascadeIndex (moveMask64 generated) (moveMask64 propagation)))).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (moveMask64 propagation + 2 * moveMask64 generated) &&& 16 > 0 then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (zip256 (· + ·) sumValue (cascadeVector (cascadeIndex (moveMask64 generated) (moveMask64 propagation)))).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel repairIndex 2 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply repair_masks_checked original.nextIdentity entered current inputs outputs frame args
      currentCall enteredWF homes authority generated propagation generatedArgument propagationArgument post
    intro generatedWord equalWord middle generatedSlot equalWordSlot generatedRead equalWordRead
      firstPreserved middleCall middleAuthority firstNext
    apply repair_index_checked original.nextIdentity entered middle inputs outputs frame args
      middleCall enteredWF homes middleAuthority generatedWord equalWord _ _
      generatedSlot equalWordSlot generatedRead equalWordRead post
    intro sumHome indexHome after sumSlot indexSlot sumRead indexRead indexBound
      indexEarlier secondPreserved afterCall afterAuthority secondNext
    obtain ⟨fuel, final, executed, result, writable, footprint⟩ := repair_lookup_final original entered after
      inputs outputs output frame args call afterCall outputMember setup enteredWF
      (Nat.le_trans advanced (Nat.le_trans firstNext secondNext)) homes afterAuthority outputArgument
      sumHome indexHome sumValue _ _ sumArgument sumSlot indexSlot sumRead indexRead indexBound
    refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
    intro id offset old notOutput
    exact (footprint id offset old notOutput).trans
      (((firstPreserved.trans secondPreserved).cells id old offset))
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms repair_tail_execution
end UInt256Proof.Add.Safety
