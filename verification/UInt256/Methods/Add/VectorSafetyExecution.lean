import UInt256.Methods.Add.VectorSafetyFinish

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Separation of the preparation helper's private outputs, supplied by its
    caller's frame allocation. Public input/output overlap remains unrestricted. -/
structure PrepareSeparation (output sum mask incoming propagation : Reference) : Prop where
  sumMask : sum.allocation ≠ mask.allocation
  sumIncoming : sum.allocation ≠ incoming.allocation
  maskIncoming : mask.allocation ≠ incoming.allocation
  sumOutput : sum.allocation ≠ output.allocation
  maskOutput : mask.allocation ≠ output.allocation
  incomingOutput : incoming.allocation ≠ output.allocation
  sumPropagation : sum.allocation ≠ propagation.allocation
  maskPropagation : mask.allocation ≠ propagation.allocation
  incomingPropagation : incoming.allocation ≠ propagation.allocation
  outputPropagation : output.allocation ≠ propagation.allocation

/-- Exact initialized snapshots produced by the helper, before its caller's
    remaining carry repair. This is not yet the full addition postcondition. -/
structure PrepareResult (memory : Memory) (output sum mask incoming propagation : Reference)
    (a b : BitVec 256) : Prop where
  sumRead : read memory sum 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) a b).toNat 32)
  maskRead : read memory mask 32 1 = .ok (numberBytes (generatedCarry a b).toNat 32)
  incomingRead : read memory incoming 32 1 = .ok (numberBytes (incomingCarry (generatedCarry a b)).toNat 32)
  outputRead : read memory output 32 1 = .ok (numberBytes
    (CIL.Vector.zip256 (· - ·) (CIL.Vector.zip256 (· + ·) a b) (incomingCarry (generatedCarry a b))).toNat 32)
  propagationRead : read memory propagation 32 1 = .ok
    (numberBytes (propagationMask (CIL.Vector.zip256 (· + ·) a b)).toNat 32)
  outputWritable : access memory output 32 1 true = .ok ()
  propagationWritable : access memory propagation 32 1 true = .ok ()

theorem vector_prepare_execution (original entered : Memory)
    (inputs outputs : List Reference) (left right output sum mask incoming propagation : Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (outputMember : output ∈ outputs) (sumMember : sum ∈ outputs)
    (maskMember : mask ∈ outputs) (incomingMember : incoming ∈ outputs) (propagationMember : propagation ∈ outputs)
    (separate : PrepareSeparation output sum mask incoming propagation)
    (leftArgument : args[0]? = some (.reference (.address left)))
    (rightArgument : args[1]? = some (.reference (.address right)))
    (outputArgument : args[2]? = some (.reference (.address output)))
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (maskArgument : args[4]? = some (.reference (.address mask)))
    (incomingArgument : args[5]? = some (.reference (.address incoming)))
    (propagationArgument : args[6]? = some (.reference (.address propagation))) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex 0 args frame [] entered = .ok (final, []) ∧
      PrepareResult final output sum mask incoming propagation (inputValue original left) (inputValue original right) ∧
      (∀ id offset, id < original.nextIdentity →
        (∀ reference ∈ [output, sum, mask, incoming, propagation], OutsideOutput reference id offset) →
        final.cells id offset = original.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [] ∧
    PrepareResult final output sum mask incoming propagation (inputValue original left) (inputValue original right) ∧
    (∀ id offset, id < original.nextIdentity →
      (∀ reference ∈ [output, sum, mask, incoming, propagation], OutsideOutput reference id offset) →
      final.cells id offset = original.cells id offset)
  have finish : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex 0 args frame [] entered = .ok (final, returned) ∧ post final returned := by
    apply vector_prepare_checked original entered inputs outputs left right sum mask incoming frame args call setup homes
      leftMember rightMember sumMember maskMember incomingMember
      separate.sumMask separate.sumIncoming separate.maskIncoming
      leftArgument rightArgument sumArgument maskArgument incomingArgument post
    intro current sumRead maskRead incomingRead currentCall authority _ prefixFootprint
    obtain ⟨fuel, final, executed, outputRead, propagationRead, outputWritable, propagationWritable, retained, footprint⟩ :=
      vector_prepare_finish original entered current inputs outputs output sum incoming propagation frame args call currentCall
        setup outputMember sumMember incomingMember propagationMember authority separate.sumOutput separate.outputPropagation
        outputArgument sumArgument incomingArgument propagationArgument
        (CIL.Vector.zip256 (· + ·) (inputValue original left) (inputValue original right))
        (incomingCarry (generatedCarry (inputValue original left) (inputValue original right))) sumRead incomingRead
    have old : ∀ reference ∈ outputs, reference.allocation < original.nextIdentity := by
      intro reference member
      obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
      exact (call.1.1.1 _ _ present).1
    refine ⟨fuel, final, [], executed, rfl, ?_, ?_⟩
    · exact ⟨retained sum 32 1 _ (old sum sumMember) separate.sumOutput separate.sumPropagation sumRead,
        retained mask 32 1 _ (old mask maskMember) separate.maskOutput separate.maskPropagation maskRead,
        retained incoming 32 1 _ (old incoming incomingMember) separate.incomingOutput separate.incomingPropagation incomingRead,
        outputRead, propagationRead, outputWritable, propagationWritable⟩
    · intro id offset older outside
      exact (footprint id offset older (outside output (by simp)) (outside propagation (by simp))).trans
        (prefixFootprint id offset older (outside sum (by simp)) (outside mask (by simp)) (outside incoming (by simp)))
  obtain ⟨fuel, final, returned, executed, result, rest⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, rest⟩

#print axioms vector_prepare_execution
end UInt256Proof.Add.Safety
