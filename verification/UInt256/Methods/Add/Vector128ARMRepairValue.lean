import UInt256.Methods.Add.Vector128ARMRepairPair

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Check the repair OR or high-result subtraction, including an initialized
    readback when the subtraction overwrites its existing private home. -/
theorem vector128_arm_repair_value (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (subtract : Bool) (left right : BitVec 128) (leftHome rightHome : Reference)
    (leftSlot : frame.locals[if subtract then 11 else 20]? = some (.bytes .vector128 leftHome))
    (rightSlot : frame.locals[if subtract then 23 else 22]? = some (.bytes .vector128 rightHome))
    (leftRead : read current leftHome 16 1 = .ok (numberBytes left.toNat 16))
    (rightRead : read current rightHome 16 1 = .ok (numberBytes right.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if subtract then 11 else 23]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (if subtract then corrected128 left right else left ||| right).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (if subtract then corrected128 left right else left ||| right).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index (if subtract then 149 else 137) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index (if subtract then 145 else 133) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have specified : vector128Specs[if subtract then 10 else 22]? = some vector128ZeroSpec := by
      cases subtract <;> rfl
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority _ vector128ZeroSpec specified
        (.v128 (if subtract then corrected128 left right else left ||| right))
        (if subtract then corrected128 left right else left ||| right).toNat rfl
    have actual : frame.locals[if subtract then 11 else 23]? = some (.bytes .vector128 reference) := by
      cases subtract <;> exact slot
    have done := continuation reference after actual loaded retained afterCall afterAuthority written
    have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 left) left.toNat rfl leftSlot leftRead
    have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 right) right.toNat rfl rightSlot rightRead
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    have profile : vector128Body.profile = Extracted.profile := by rfl
    cases subtract <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadLeft loadRight done ⊢
    all_goals
      repeat' first
        | exact done
        | (apply run_next_exists post found (by rfl)
           first
           | exact loadLeft _ _
           | exact loadRight _ _
           | exact stored _ _ _
           | (simp (config := { implicitDefEqProofs := false })
               [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
                 CIL.Vector.intrinsic_sub128, CIL.Vector.intrinsic_or128, corrected128,
                 checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
              first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_repair_value
end UInt256Proof.Add.Safety
