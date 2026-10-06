import UInt256.Methods.Subtract.VectorSafetyLookupFinal

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- Complete the propagation branch from saved vector masks through checked
    index arithmetic, lookup, correction and mathematical underflow return. -/
theorem vector_cascade_execution (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (enteredWF : entered.WellFormed)
    (advanced : entered.nextIdentity ≤ current.nextIdentity)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (differenceHome maskHome equalHome : Reference) (a b : Limbs)
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (maskSlot : frame.locals[3]? = some (.bytes .vector256 maskHome))
    (equalSlot : frame.locals[5]? = some (.bytes .vector256 equalHome))
    (differenceRead : read current differenceHome 32 1 =
      .ok (numberBytes (zip256 (· - ·) (value a) (value b)).toNat 32))
    (maskRead : read current maskHome 32 1 =
      .ok (numberBytes (generatedBorrow (value a) (value b)).toNat 32))
    (equalRead : read current equalHome 32 1 =
      .ok (numberBytes (equalLanes (value a) (value b)).toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex (vectorTestStart + 4) args frame [] current =
        .ok (final, [.scalar (.i32 (if (value a).toNat < (value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (value a - value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (value a).toNat < (value b).toNat then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (value a - value b).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 4) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_movemasks_checked original.nextIdentity entered current inputs outputs frame args
      currentCall enteredWF homes authority maskHome equalHome
      (generatedBorrow (value a) (value b)) (equalLanes (value a) (value b))
      maskSlot equalSlot maskRead equalRead post
    intro generatedWord equalWord middle generatedSlot equalWordSlot generatedRead equalWordRead
      earlier firstPreserved middleCall middleAuthority firstNext
    have firstOrder := homes.ordered 2 6 .vector256 .word32 differenceHome generatedWord
      (by decide) differenceSlot generatedSlot
    have retainedDifference := (earlier.read differenceHome firstOrder 32 1).trans differenceRead
    apply vector_index_checked original.nextIdentity entered middle inputs outputs frame args
      middleCall enteredWF homes middleAuthority generatedWord equalWord _ _
      generatedSlot equalWordSlot generatedRead equalWordRead post
    intro sumHome indexHome after sumSlot indexSlot sumRead indexRead indexBound
      indexEarlier secondPreserved afterCall afterAuthority secondNext
    have secondOrder := homes.ordered 2 6 .vector256 .word32 differenceHome sumHome
      (by decide) differenceSlot sumSlot
    have finalDifference := (indexEarlier.read differenceHome secondOrder 32 1).trans retainedDifference
    obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_lookup_final original entered after
      inputs outputs output frame args call afterCall outputMember setup enteredWF
      (Nat.le_trans advanced (Nat.le_trans firstNext secondNext)) homes afterAuthority outputArgument
      differenceHome sumHome indexHome a b differenceSlot sumSlot indexSlot
      finalDifference sumRead indexRead indexBound
    refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
    intro id offset old notOutput
    exact (footprint id offset old notOutput).trans
      (((firstPreserved.trans secondPreserved).cells id old offset))
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_cascade_execution
end UInt256Proof.Subtract.Safety
