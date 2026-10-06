import UInt256.Methods.Add.Vector128Sum

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def halfCarry (sum left : BitVec 128) : BitVec 128 :=
  CIL.Vector.zip128 (fun x y => CIL.Vector.mask64 (x.ult y)) sum left

/-- Both extracted carry-mask blocks compare a saved lane sum with its initial
    left operand. The lower sum remains on the stack across each private store. -/
theorem vector128_carry_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high left : BitVec 128) (sumHome leftHome : Reference)
    (sumSlot : frame.locals[5]? = some (.bytes .vector128 sumHome))
    (leftSlot : frame.locals[if upper then 2 else 1]? = some (.bytes .vector128 leftHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (leftRead : read current leftHome 16 1 = .ok (numberBytes left.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if upper then 7 else 6]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (halfCarry (if upper then high else low) left).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfCarry (if upper then high else low) left).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (if upper then 37 else 33) args frame
          [.scalar (.v128 low)] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (if upper then 33 else 29) args frame
        [.scalar (.v128 low)] current = .ok (result, returned) ∧ post result returned := by
  have specified : vector128Specs[if upper then 6 else 5]? = some vector128ZeroSpec := by
    cases upper <;> rfl
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (halfCarry (if upper then high else low) left))
      (halfCarry (if upper then high else low) left).toNat rfl
  have actual : frame.locals[if upper then 7 else 6]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 left) left.toNat rfl leftSlot leftRead
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl sumSlot sumRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadLeft done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact loadLeft _ _
         | exact loadSum _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_lt128, halfCarry, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_carry_checked
end UInt256Proof.Add.Safety
