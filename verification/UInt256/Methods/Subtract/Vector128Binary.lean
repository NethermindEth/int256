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
