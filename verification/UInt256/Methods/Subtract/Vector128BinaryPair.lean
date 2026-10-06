import UInt256.Methods.AddSubtract.Vector128Prefix
import CIL.SIMD.EvaluationLemmas

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128BinaryValue (borrow : Bool) (a b : BitVec 128) : BitVec 128 :=
  if borrow then CIL.Vector.zip128 (fun x y => CIL.Vector.mask64 (x.ult y)) a b
  else CIL.Vector.zip128 (· - ·) a b

/-- Each actual lane-difference or borrow-mask instruction stores into a fresh
    numeric home, retaining caller memory and all existing access authority. -/
theorem vector128_binary_checked (borrow upper : Bool) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (a b : BitVec 128) (leftHome rightHome : Reference)
    (leftSlot : frame.locals[if upper then 2 else 1]? = some (.bytes .vector128 leftHome))
    (rightSlot : frame.locals[if upper then 4 else 3]? = some (.bytes .vector128 rightHome))
    (leftRead : read current leftHome 16 1 = .ok (numberBytes a.toNat 16))
    (rightRead : read current rightHome 16 1 = .ok (numberBytes b.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[(if borrow then 6 else 4) + (if upper then 1 else 0) + 1]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (vector128BinaryValue borrow a b).toNat 16) →
      MemoryBelow boundary current after → CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (vector128BinaryValue borrow a b).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index ((if borrow then 30 else 22) + (if upper then 4 else 0) + 4)
          args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index ((if borrow then 30 else 22) + (if upper then 4 else 0))
        args frame [] current = .ok (final, returned) ∧ post final returned := by
  have specified : vector128Specs[(if borrow then 6 else 4) + (if upper then 1 else 0)]? =
      some vector128ZeroSpec := by cases borrow <;> cases upper <;> rfl
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (vector128BinaryValue borrow a b)) (vector128BinaryValue borrow a b).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 a) a.toNat rfl leftSlot leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 b) b.toNat rfl rightSlot rightRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  cases borrow <;> cases upper <;>
    simp only [vector128BinaryValue, Bool.false_eq_true, ite_false, ite_true, Nat.reduceAdd] at stored loadLeft loadRight done ⊢
  all_goals
    apply run_next_exists post found (by rfl) (loadLeft _ _)
    apply run_next_exists post found (by rfl) (loadRight _ _)
    apply run_next_exists post found (by rfl)
    · simp (config := { implicitDefEqProofs := false })
        [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
          CIL.Vector.intrinsic_sub128, CIL.Vector.intrinsic_lt128,
          checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · apply run_next_exists post found (by rfl) (stored _ _ _)
      exact done

#print axioms vector128_binary_checked
end UInt256Proof.Subtract.Safety

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
