import UInt256.Methods.Subtract.VectorSafetyCascadeFinal

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
