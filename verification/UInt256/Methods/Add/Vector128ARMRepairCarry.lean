import UInt256.Methods.Add.Vector128ARMRepairValue
import UInt256.Methods.AddSubtract.Vector128Overwrite

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def repaired128Carry (carry propagation full repair : BitVec 128) : BitVec 128 :=
  carry ||| (propagation ||| (full &&& repair))

/-- Update the saved high carry mask from initialized private snapshots. -/
theorem vector128_arm_repair_carry (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (carry : BitVec 128) (carryHome : Reference)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (propagation : BitVec 128) (propagationHome : Reference)
    (propagationSlot : frame.locals[13]? = some (.bytes .vector128 propagationHome))
    (propagationRead : read current propagationHome 16 1 = .ok (numberBytes propagation.toNat 16))
    (full : BitVec 128) (fullHome : Reference)
    (fullSlot : frame.locals[21]? = some (.bytes .vector128 fullHome))
    (fullRead : read current fullHome 16 1 = .ok (numberBytes full.toNat 16))
    (repair : BitVec 128) (repairHome : Reference)
    (repairSlot : frame.locals[23]? = some (.bytes .vector128 repairHome))
    (repairRead : read current repairHome 16 1 = .ok (numberBytes repair.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[7]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (repaired128Carry carry propagation full repair).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (repaired128Carry carry propagation full repair).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 145 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 137 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 6 vector128ZeroSpec (by rfl)
        (.v128 (repaired128Carry carry propagation full repair))
        (repaired128Carry carry propagation full repair).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have load_carry := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 carry) carry.toNat rfl carrySlot carryRead
    have load_propagation := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 propagation) propagation.toNat rfl propagationSlot propagationRead
    have load_full := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 full) full.toNat rfl fullSlot fullRead
    have load_repair := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 repair) repair.toNat rfl repairSlot repairRead
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    have profile : vector128Body.profile = Extracted.profile := by rfl
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact load_carry _ _
         | exact load_propagation _ _
         | exact load_full _ _
         | exact load_repair _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, enabled, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_or128, repaired128Carry,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_repair_carry
end UInt256Proof.Add.Safety
