import UInt256.Methods.Subtract.VectorSafetyReturn
import UInt256.Methods.Reporting.VectorArithmetic
import UInt256.Methods.Subtract.VectorSafetyCorrection
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- The two actual vector masks encode the independent limb borrow predicates. -/
theorem vector_generated_mask (a b : Limbs) :
    moveMask64 (generatedBorrow (value a) (value b)) = operationMask (subtractGenerate a b) := by
  simp only [generatedBorrow, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, moveMask_flags,
    operationMask, subtractGenerate]

theorem vector_propagated_mask (a b : Limbs) :
    moveMask64 (equalLanes (value a) (value b)) = operationMask (subtractPropagate a b) := by
  simp only [equalLanes, UInt256Proof.Equality.value_pack, zip256,
    lane256_0, lane256_1, lane256_2, lane256_3, moveMask_flags,
    operationMask, subtractPropagate]

/-- The correction vector produces full-width modular subtraction, independently
    of the extracted instruction sequence. -/
theorem vector_cascade_difference (a b : Limbs) :
    zip256 (· - ·) (zip256 (· - ·) (value a) (value b))
      (cascadeVector (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b))))) = value a - value b := by
  rw [vector_generated_mask, vector_propagated_mask]
  have lanes : zip256 (· - ·) (value a) (value b) = packedLimbs (fun i => a i - b i) := by
    simp only [UInt256Proof.Equality.value_pack, zip256, packedLimbs,
      lane256_0, lane256_1, lane256_2, lane256_3]
  rw [lanes, subtract_cascade_vector]
  change pack256 _ _ _ _ = _
  rw [← UInt256Proof.Equality.value_pack, UInt256Proof.four_limb_difference]

/-- The scalar cascade bit is precisely unsigned underflow of the initial values. -/
theorem vector_cascade_underflow (a b : Limbs) :
    (if (moveMask64 (equalLanes (value a) (value b)) +
        2 * moveMask64 (generatedBorrow (value a) (value b))) &&& 16 > 0
      then (1 : BitVec 32) else 0) =
      if (value a).toNat < (value b).toNat then 1 else 0 := by
  rw [vector_generated_mask, vector_propagated_mask]
  have positive (x : BitVec 32) : x > 0 ↔ x ≠ 0 := by
    exact UInt256Proof.Reporting.flag32_positive x
  simp only [positive, UInt256Proof.Reporting.cascade_subtract_flag,
    UInt256Proof.Reporting.finalBorrow_underflow]

#print axioms vector_generated_mask
#print axioms vector_propagated_mask
#print axioms vector_cascade_difference
#print axioms vector_cascade_underflow
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- Correct the output and return the mathematical underflow flag. Frame expiry
    preserves the output and every other caller allocation. -/
theorem vector_cascade_final (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (differenceHome sumHome correctionHome : Reference) (a b : Limbs)
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (sumSlot : frame.locals[6]? = some (.bytes .word32 sumHome))
    (correctionSlot : frame.locals[8]? = some (.bytes .vector256 correctionHome))
    (differenceRead : read current differenceHome 32 1 =
      .ok (numberBytes (zip256 (· - ·) (value a) (value b)).toNat 32))
    (sumRead : read current sumHome 4 1 = .ok (numberBytes
      (moveMask64 (equalLanes (value a) (value b)) +
        2 * moveMask64 (generatedBorrow (value a) (value b))).toNat 4))
    (correctionRead : read current correctionHome 32 1 = .ok (numberBytes
      (cascadeVector (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b))))).toNat 32)) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex (vectorTestStart + 34) args frame [] current =
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
      run Extracted.program fuel vectorIndex (vectorTestStart + 34) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_correction_output_checked original entered current inputs outputs output frame args
      call currentCall outputMember authority outputArgument differenceHome correctionHome
      (zip256 (· - ·) (value a) (value b))
      (cascadeVector (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b)))))
      differenceSlot correctionSlot differenceRead correctionRead post
    intro after readback afterCall _ outside privateReads _
    have retainedSum := privateReads _ _ _ _ (homes.home_bound 6 _ _ sumSlot) sumRead
    have executed := vector_cascade_return after frame args sumHome _ sumSlot retainedSum
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨vectorCascadeFuel, leaveFrame frame after, _, executed, ?_, ?_, ?_, ?_⟩
    · rw [vector_cascade_underflow]
    · obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
      have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
      rw [teardown.read output old 32 1]
      rw [vector_cascade_difference] at readback
      exact readback
    · obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
      have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
      exact (teardown.access output old 32 1 true).trans
        (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, outputMember, rfl⟩))
    · intro id offset old notOutput
      exact (teardown.cells id old offset).trans (outside id offset notOutput)
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_cascade_final
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
open UInt256Model CIL.Vector UInt256Proof.SIMD

/-- Compose first-use or cached lookup allocation, bounded vector load,
    correction and return while retaining the saved lane differences and sum. -/
theorem vector_lookup_final (original entered current : Memory)
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
    (differenceHome sumHome indexHome : Reference) (a b : Limbs)
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (sumSlot : frame.locals[6]? = some (.bytes .word32 sumHome))
    (indexSlot : frame.locals[7]? = some (.bytes .word32 indexHome))
    (differenceRead : read current differenceHome 32 1 =
      .ok (numberBytes (zip256 (· - ·) (value a) (value b)).toNat 32))
    (sumRead : read current sumHome 4 1 = .ok (numberBytes
      (moveMask64 (equalLanes (value a) (value b)) +
        2 * moveMask64 (generatedBorrow (value a) (value b))).toNat 4))
    (indexRead : read current indexHome 4 1 = .ok (numberBytes
      (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b)))).toNat 4))
    (indexBound : (cascadeIndex (moveMask64 (generatedBorrow (value a) (value b)))
        (moveMask64 (equalLanes (value a) (value b)))).toNat < 16) :
    ∃ fuel final,
      run Extracted.program fuel vectorIndex (vectorTestStart + 26) args frame [] current =
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
  have callerBound := (enterFrame_fresh _ _ _ _ _ setup).1.next
  have oldHome (i : Nat) (spec : NumericLocalSpec) (reference : Reference)
      (specified : vectorSpecs[i]? = some spec)
      (slot : frame.locals[i]? = some (.bytes spec.kind reference)) :
      reference.allocation < current.nextIdentity := by
    obtain ⟨r, found, _, _, writable⟩ := homes.home_at i spec specified
    have same : reference = r := by simpa only [slot, Option.some.injEq, LocalSlot.bytes.injEq, true_and] using found
    subst r
    obtain ⟨allocation, ready⟩ := access_requirements writable
    exact Nat.lt_of_lt_of_le (enteredWF.1 _ _ ready.present).1 advanced
  have differenceOld := oldHome 2 vectorZeroSpec differenceHome (by rfl) differenceSlot
  have sumOld := oldHome 6 vectorWordZero sumHome (by rfl) sumSlot
  have indexOld := oldHome 7 vectorWordZero indexHome (by rfl) indexSlot
  have finish : ∃ fuel final returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 26) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
    apply vector_lookup_call current inputs outputs frame args currentCall post
    intro withTable table valid tablePreserved tableCall
    have tableAuthority := authority.trans (tablePreserved.weaken advanced).accessBelow
    apply vector_lookup_load original.nextIdentity entered withTable inputs outputs frame args
      tableCall enteredWF homes tableAuthority table indexHome _ valid indexBound indexSlot
      ((tablePreserved.read indexHome indexOld 4 1).trans indexRead) post
    intro correctionHome after correctionSlot correctionRead earlier preserved afterCall afterAuthority
    have differenceOrder := homes.ordered 2 8 .vector256 .vector256 differenceHome correctionHome
      (by decide) differenceSlot correctionSlot
    have sumOrder := homes.ordered 6 8 .word32 .vector256 sumHome correctionHome
      (by decide) sumSlot correctionSlot
    have retainedDifference := (earlier.read differenceHome differenceOrder 32 1).trans
      ((tablePreserved.read differenceHome differenceOld 32 1).trans differenceRead)
    have retainedSum := (earlier.read sumHome sumOrder 4 1).trans
      ((tablePreserved.read sumHome sumOld 4 1).trans sumRead)
    obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_cascade_final original entered after
      inputs outputs output frame args call afterCall outputMember setup homes afterAuthority outputArgument
      differenceHome sumHome correctionHome a b differenceSlot sumSlot correctionSlot
      retainedDifference retainedSum correctionRead
    refine ⟨fuel, final, _, executed, rfl, result, writable, ?_⟩
    intro id offset old notOutput
    exact (footprint id offset old notOutput).trans ((preserved.cells id old offset).trans
      (tablePreserved.cells id (Nat.lt_of_lt_of_le old (Nat.le_trans callerBound advanced)) offset))
  obtain ⟨fuel, final, returned, executed, flag, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_lookup_final
end UInt256Proof.Subtract.Safety

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
