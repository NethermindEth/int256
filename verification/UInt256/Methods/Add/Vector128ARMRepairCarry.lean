import UInt256.Methods.Add.Vector128ARMRepairExtra
import UInt256.Methods.AddSubtract.Vector128Overwrite

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Both extra-propagation stores, preserving all earlier private snapshots. -/
theorem vector128_arm_extra_pair (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (result propagation : BitVec 128) (resultHome propagationHome : Reference)
    (resultSlot : slots[10]? = some (.bytes .vector128 resultHome))
    (propagationSlot : slots[19]? = some (.bytes .vector128 propagationHome))
    (resultRead : read current resultHome 16 1 = .ok (numberBytes result.toNat 16))
    (propagationRead : read current propagationHome 16 1 = .ok (numberBytes propagation.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ fullHome extraHome after,
      slots[20]? = some (.bytes .vector128 fullHome) →
      slots[21]? = some (.bytes .vector128 extraHome) →
      read after fullHome 16 1 = .ok (numberBytes (full128 result).toNat 16) →
      read after extraHome 16 1 = .ok (numberBytes (incoming128Low (full128 result &&& propagation)).toNat 16) →
      (∀ i, i < 20 → ∀ reference bytes, slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 133 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 122 args frame [] current = .ok (final, returned) ∧ post final returned := by
  have actualResult : frame.locals[11]? = some (.bytes .vector128 resultHome) := by simpa [layout] using resultSlot
  have actualPropagation : frame.locals[20]? = some (.bytes .vector128 propagationHome) := by simpa [layout] using propagationSlot
  apply vector128_arm_full_mask enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority result resultHome actualResult resultRead post
  intro fullHome middle fullSlot fullRead preserved middleCall middleAuthority firstWrite
  have fullTail : slots[20]? = some (.bytes .vector128 fullHome) := by simpa [layout] using fullSlot
  have savedPropagation := vector128_prior_read entered current middle boundary slots homes 19 20 (by decide)
    propagationHome fullHome propagationSlot fullTail _ _ firstWrite propagationRead
  apply vector128_arm_extra_mask enabled boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority (full128 result) fullHome fullSlot fullRead
    propagation propagationHome actualPropagation savedPropagation post
  intro extraHome after extraSlot extraRead kept afterCall afterAuthority secondWrite
  have extraTail : slots[21]? = some (.bytes .vector128 extraHome) := by simpa [layout] using extraSlot
  have savedFull := vector128_prior_read entered middle after boundary slots homes 20 21 (by decide)
    fullHome extraHome fullTail extraTail _ _ secondWrite fullRead
  have earlier : ∀ i, i < 20 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read entered middle after boundary slots homes i 21 (by omega)
      reference extraHome slot extraTail _ _ secondWrite
      (vector128_prior_read entered current middle boundary slots homes i 20 bound
        reference fullHome slot fullTail _ _ firstWrite loaded)
  exact continuation fullHome extraHome after fullTail extraTail savedFull extraRead earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_arm_extra_pair
end UInt256Proof.Add.Safety

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
