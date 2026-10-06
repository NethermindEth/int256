import UInt256.Methods.Subtract.VectorSafetyBranches

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Model

/-- Checked early output and both repair branches retain saved initial operands
    under arbitrary valid caller overlap. -/
theorem vector_output_execution (original entered current : Memory)
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
    (leftHome rightHome differenceHome maskHome incomingHome : Reference) (a b : UInt256Model.Limbs)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (maskSlot : frame.locals[3]? = some (.bytes .vector256 maskHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes (UInt256Model.value a).toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes (UInt256Model.value b).toNat 32))
    (differenceRead : read current differenceHome 32 1 = .ok (numberBytes
      (CIL.Vector.zip256 (· - ·) (UInt256Model.value a) (UInt256Model.value b)).toNat 32))
    (maskRead : read current maskHome 32 1 = .ok (numberBytes
      (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)).toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes
      (incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b))).toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (final, [.scalar (.i32 (if (UInt256Model.value a).toNat < (UInt256Model.value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (UInt256Model.value a - UInt256Model.value b).toNat 32) ∧
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
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_early_output_checked original entered current inputs outputs output frame args call currentCall
      outputMember authority outputArgument differenceHome incomingHome
      (CIL.Vector.zip256 (· - ·) (value a) (value b))
      (incomingBorrow (generatedBorrow (value a) (value b)))
      differenceSlot incomingSlot differenceRead incomingRead post
    intro after readback afterCall afterAuthority outside privateReads next
    obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_branches_final original entered after
      inputs outputs output frame args call afterCall outputMember setup enteredWF (Nat.le_trans advanced next)
      homes afterAuthority outputArgument leftHome rightHome differenceHome maskHome incomingHome a b
      leftSlot rightSlot differenceSlot maskSlot incomingSlot
      (privateReads _ _ _ _ (homes.home_bound 0 _ _ leftSlot) leftRead)
      (privateReads _ _ _ _ (homes.home_bound 1 _ _ rightSlot) rightRead)
      (privateReads _ _ _ _ (homes.home_bound 2 _ _ differenceSlot) differenceRead)
      (privateReads _ _ _ _ (homes.home_bound 3 _ _ maskSlot) maskRead)
      (privateReads _ _ _ _ (homes.home_bound 4 _ _ incomingSlot) incomingRead) readback
    refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
    intro id offset old notOutput
    exact (footprint id offset old notOutput).trans (outside id offset notOutput)
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_output_execution
end UInt256Proof.Subtract.Safety
