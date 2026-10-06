import UInt256.Methods.Add.VectorRepairOutput

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Checked correction store through normal return, preserving the caller's
    initialized writable output when the helper's private frame expires. -/
theorem repair_final (original entered current : Memory)
    (inputs outputs : List Reference) (output sumHome correctionHome : Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame repairBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (sumValue correctionValue : BitVec 256) (sum : BitVec 32)
    (outputArgument : args[3]? = some (.reference (.address output)))
    (sumArgument : args[0]? = some (.scalar (.v256 sumValue)))
    (sumSlot : frame.locals[0]? = some (.bytes .word32 sumHome))
    (correctionSlot : frame.locals[2]? = some (.bytes .vector256 correctionHome))
    (sumRead : read current sumHome 4 1 = .ok (numberBytes sum.toNat 4))
    (correctionRead : read current correctionHome 32 1 = .ok (numberBytes correctionValue.toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel repairIndex 32 args frame [] current =
        .ok (final, [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel repairIndex 32 args frame [] current = .ok (final, returned) ∧ post final returned := by
    apply repair_output_checked original entered current inputs outputs output correctionHome frame args
      call currentCall outputMember authority outputArgument sumValue correctionValue sumArgument
      correctionSlot correctionRead post
    intro after _ readback afterCall _ outside privateReads _
    have retainedSum := privateReads _ _ _ _ (homes.home_bound 0 _ _ sumSlot) sumRead
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    refine ⟨6, leaveFrame frame after, _, repair_return after frame args sumHome sum sumSlot retainedSum,
      rfl, ?_, ?_, ?_⟩
    · exact (teardown.read output old 32 1).trans readback
    · exact (teardown.access output old 32 1 true).trans
        (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, outputMember, rfl⟩))
    · intro id offset old notOutput
      exact (teardown.cells id old offset).trans (outside id offset notOutput)
  obtain ⟨fuel, final, returned, executed, same, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms repair_final
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- Compose first-use or cached lookup allocation, bounded vector load,
    correction and return while retaining the initialized scalar sum. -/
theorem repair_lookup_final (original entered current : Memory)
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
    (sumHome indexHome : Reference) (sumValue : BitVec 256) (sum index : BitVec 32)
    (sumArgument : args[0]? = some (.scalar (.v256 sumValue)))
    (sumSlot : frame.locals[0]? = some (.bytes .word32 sumHome))
    (indexSlot : frame.locals[1]? = some (.bytes .word32 indexHome))
    (sumRead : read current sumHome 4 1 = .ok (numberBytes sum.toNat 4))
    (indexRead : read current indexHome 4 1 = .ok (numberBytes index.toNat 4))
    (indexBound : index.toNat < 16) :
    ∃ fuel final,
      run Extracted.program fuel repairIndex 24 args frame [] current =
        .ok (final, [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (zip256 (· + ·) sumValue (cascadeVector index)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (zip256 (· + ·) sumValue (cascadeVector index)).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have callerBound := (enterFrame_fresh _ _ _ _ _ setup).1.next
  have oldHome (i : Nat) (spec : NumericLocalSpec) (reference : Reference)
      (specified : repairSpecs[i]? = some spec)
      (slot : frame.locals[i]? = some (.bytes spec.kind reference)) :
      reference.allocation < current.nextIdentity := by
    obtain ⟨r, found, _, _, writable⟩ := homes.home_at i spec specified
    have same : reference = r := by simpa only [slot, Option.some.injEq, LocalSlot.bytes.injEq, true_and] using found
    subst r
    obtain ⟨allocation, ready⟩ := access_requirements writable
    exact Nat.lt_of_lt_of_le (enteredWF.1 _ _ ready.present).1 advanced
  have sumOld := oldHome 0 cascadeWordZero sumHome (by rfl) sumSlot
  have indexOld := oldHome 1 cascadeWordZero indexHome (by rfl) indexSlot
  have finish : ∃ fuel final returned,
      run Extracted.program fuel repairIndex 24 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply repair_lookup_call current inputs outputs frame args currentCall post
    intro withTable table valid tablePreserved tableCall
    have tableAuthority := authority.trans (tablePreserved.weaken advanced).accessBelow
    apply repair_lookup_load original.nextIdentity entered withTable inputs outputs frame args
      tableCall enteredWF homes tableAuthority table indexHome _ valid indexBound indexSlot
      ((tablePreserved.read indexHome indexOld 4 1).trans indexRead) post
    intro correctionHome after correctionSlot correctionRead earlier preserved afterCall afterAuthority
    have sumOrder := homes.ordered 0 2 .word32 .vector256 sumHome correctionHome
      (by decide) sumSlot correctionSlot
    have retainedSum := (earlier.read sumHome sumOrder 4 1).trans
      ((tablePreserved.read sumHome sumOld 4 1).trans sumRead)
    obtain ⟨fuel, final, executed, result, writable, footprint⟩ := repair_final original entered after
      inputs outputs output sumHome correctionHome frame args call afterCall outputMember setup homes afterAuthority
      sumValue (cascadeVector index) sum outputArgument sumArgument sumSlot correctionSlot retainedSum correctionRead
    refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
    intro id offset old notOutput
    exact (footprint id offset old notOutput).trans ((preserved.cells id old offset).trans
      (tablePreserved.cells id (Nat.lt_of_lt_of_le old (Nat.le_trans callerBound advanced)) offset))
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms repair_lookup_final
end UInt256Proof.Add.Safety

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
