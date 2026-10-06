import UInt256.Methods.AddSubtract.Vector128Prefix
import CIL.SIMD.EvaluationLemmas

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def halfSum (a b : BitVec 128) : BitVec 128 := CIL.Vector.zip128 (· + ·) a b

/-- Compute both lane sums from the four initialized snapshots, keeping the
    lower sum on the stack and storing the upper sum in its actual private home. -/
theorem vector128_sum_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[5]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (halfSum (values 1) (values 3)).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfSum (values 1) (values 3)).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 29 args frame
          [.scalar (.v128 (halfSum (values 0) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 4 vector128ZeroSpec (by rfl)
      (.v128 (halfSum (values 1) (values 3))) (halfSum (values 1) (values 3)).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have load := fun (i : Fin 4) (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 (values i)) (values i).toNat rfl (located i) (readable i)
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact load 0 _ _
       | exact load 1 _ _
       | exact load 2 _ _
       | exact load 3 _ _
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_add128, halfSum, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_sum_checked
end UInt256Proof.Add.Safety
