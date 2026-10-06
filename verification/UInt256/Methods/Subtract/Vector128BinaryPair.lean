import UInt256.Methods.Subtract.Vector128Binary

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Store both halves of a difference or borrow mask while preserving all
    earlier snapshots, including those needed when output overlaps an input. -/
theorem vector128_binary_pair (borrow : Bool) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ low high after,
      slots[if borrow then 6 else 4]? = some (.bytes .vector128 low) →
      slots[(if borrow then 6 else 4) + 1]? = some (.bytes .vector128 high) →
      read after low 16 1 = .ok (numberBytes (vector128BinaryValue borrow (values 0) (values 2)).toNat 16) →
      read after high 16 1 = .ok (numberBytes (vector128BinaryValue borrow (values 1) (values 3)).toNat 16) →
      (∀ i, i < (if borrow then 6 else 4) → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) → read current reference 16 1 = .ok bytes →
          read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after → CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index (if borrow then 38 else 30) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index (if borrow then 30 else 22) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have actual (i : Fin 4) : frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)) := by
    simpa [layout] using located i
  have baseBound : 4 ≤ (if borrow then 6 else 4) := by cases borrow <;> decide
  have first := vector128_binary_checked borrow false boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority (values 0) (values 2) (locations 0) (locations 2)
    (actual 0) (actual 2) (readable 0) (readable 2) post
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at first
  apply first
  intro low middle lowLocal lowRead preserved middleCall middleAuthority firstWrite
  have lowSlot : slots[if borrow then 6 else 4]? = some (.bytes .vector128 low) := by
    simpa [layout] using lowLocal
  have saved (i : Fin 4) : read middle (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) :=
    vector128_prior_read entered current middle boundary slots homes i.val _ (by omega)
      (locations i) low (located i) lowSlot _ _ firstWrite (readable i)
  have second := vector128_binary_checked borrow true boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority (values 1) (values 3) (locations 1) (locations 3)
    (actual 1) (actual 3) (saved 1) (saved 3) post
  simp only [ite_true] at second
  apply second
  intro high after highLocal highRead retained afterCall afterAuthority secondWrite
  have highSlot : slots[(if borrow then 6 else 4) + 1]? = some (.bytes .vector128 high) := by
    simpa [layout] using highLocal
  have savedLow := vector128_prior_read entered middle after boundary slots homes _ _ (Nat.lt_succ_self _)
    low high lowSlot highSlot _ _ secondWrite lowRead
  have earlier : ∀ i, i < (if borrow then 6 else 4) → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) → read current reference 16 1 = .ok bytes →
        read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read entered middle after boundary slots homes i _ (by omega)
      reference high slot highSlot _ _ secondWrite
      (vector128_prior_read entered current middle boundary slots homes i _ bound reference low slot lowSlot _ _ firstWrite loaded)
  have done := continuation low high after lowSlot highSlot savedLow highRead earlier (preserved.trans retained)
    afterCall afterAuthority (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)
  cases borrow <;> simpa using done

#print axioms vector128_binary_pair
end UInt256Proof.Subtract.Safety
