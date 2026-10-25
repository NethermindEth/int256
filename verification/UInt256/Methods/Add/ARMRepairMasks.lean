import CIL.Safety.SymbolicExecution
import CIL.Safety.ReturnArity
import UInt256.Methods.Add.Vector128FastEntry

namespace UInt256Proof.Add.Safety
def armRepairCode : List CIL.Op := [
.arg 3 (some .unsigned8),
.brnonzero 117,
.local 14,
.branch 121,
.local 12,
.local 13,
.const32 1,
.intrinsic (.advSimd .extract64) 3,
.setLocal 20,
.local 11,
.intrinsic (.vector (.ones 128)) 0,
.intrinsic (.vector (.eq64 128)) 2,
.setLocal 21,
.intrinsic (.vector (.zero 128)) 0,
.local 21,
.local 20,
.intrinsic (.vector (.band 128)) 2,
.const32 1,
.intrinsic (.advSimd .extract64) 3,
.setLocal 22,
.local 20,
.local 22,
.intrinsic (.vector (.bor 128)) 2,
.setLocal 23,
.local 7,
.local 13,
.local 21,
.local 23,
.intrinsic (.vector (.band 128)) 2,
.intrinsic (.vector (.bor 128)) 2,
.intrinsic (.vector (.bor 128)) 2,
.setLocal 7,
.local 11,
.local 23,
.intrinsic (.vector (.sub64 128)) 2,
.setLocal 11,
.arg 2,
.memory .asRef,
.const32 1,
.memory (.add 16 true),
.local 11,
.memory .store128,
.local 7,
.const32 1,
.intrinsic (.vector (.extract64 128)) 2,
.const32 0,
.convI8,
.gtu,
.ret (some .unsigned8)
]
end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector CIL.Vector

/-- ARM reuses the saved sum-only condition or extracts the two propagation lanes, depending on the reporting flag, then initializes repair local20. -/
theorem vector128_arm_repair_mask (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode))
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec) (enabled : body.profile.advSimd = true) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (argument : args[3]? = some (.scalar (.i32 flag)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[12]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[13]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (conditionHome : Reference)
    (conditionSlot : frame.locals[14]? = some (.bytes .vector128 conditionHome))
    (conditionRead : read current conditionHome 16 1 = .ok
      (numberBytes (selectedPropagation128 body.profile.advSimd flag low high).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[20]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (incoming128High low high).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (incoming128High low high).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method 122 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 113 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  first
  | solve | simp [body.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 19 vector128ZeroSpec (repairSpecs 0)
        (.v128 (incoming128High low high)) (incoming128High low high).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
    have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 high) high.toNat rfl highSlot highRead
    have loadCondition := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 (selectedPropagation128 body.profile.advSimd flag low high)) (selectedPropagation128 body.profile.advSimd flag low high).toNat
      rfl conditionSlot conditionRead
    by_cases zero : flag = BitVec.ofNat 32 0
    all_goals
      simp only [selectedPropagation128, enabled, zero, and_true, and_false, ite_true, ite_false,
        true_and] at loadCondition
      repeat' first
        | exact done
        | (simp (config := { failIfUnchanged := false })
             [flagFit, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero]
           apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
           first
           | exact loadCondition _ _
           | exact loadLow _ _
           | exact loadHigh _ _
           | exact stored _ _ _
           | (simp (config := { implicitDefEqProofs := false })
               [localResult, checkedIntrinsic, step, cil_guard, observerCount, enabled, flagFit, argument, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
                 CIL.Intrinsic.available, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_adv_extract,
                 incoming128_arm_high, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero,
                 checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
              first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_repair_mask
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector CIL.Vector

def full128 (result : BitVec 128) : BitVec 128 :=
  CIL.Vector.zip128 (fun x y => CIL.Vector.mask64 (x == y)) result (~~~0)

theorem vector128_arm_full_mask (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode))
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec) (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (result : BitVec 128) (resultHome : Reference)
    (resultSlot : frame.locals[11]? = some (.bytes .vector128 resultHome))
    (resultRead : read current resultHome 16 1 = .ok (numberBytes result.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[21]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (full128 result).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (full128 result).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method 126 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 122 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [body.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 20 vector128ZeroSpec (repairSpecs 1)
        (.v128 (full128 result)) (full128 result).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have load_result := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 result) result.toNat rfl resultSlot resultRead
    have ones : CIL.evalIntrinsic (.vector (.ones 128)) [] = some (.v128 (~~~0)) := by rfl
    repeat' first
      | exact done
      | (apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
         first
         | exact load_result _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, checkedIntrinsic, step, cil_guard, observerCount, enabled, pureArity, scalars, CIL.step.eq_def,
               CIL.Intrinsic.available, ones, CIL.Vector.intrinsic_eq128, full128,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_full_mask

theorem vector128_arm_extra_mask (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode))
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec) (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (full : BitVec 128) (fullHome : Reference)
    (fullSlot : frame.locals[21]? = some (.bytes .vector128 fullHome))
    (fullRead : read current fullHome 16 1 = .ok (numberBytes full.toNat 16))
    (propagation : BitVec 128) (propagationHome : Reference)
    (propagationSlot : frame.locals[20]? = some (.bytes .vector128 propagationHome))
    (propagationRead : read current propagationHome 16 1 = .ok (numberBytes propagation.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[22]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (incoming128Low (full &&& propagation)).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (incoming128Low (full &&& propagation)).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method 133 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 126 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [body.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 21 vector128ZeroSpec (repairSpecs 2)
        (.v128 (incoming128Low (full &&& propagation))) (incoming128Low (full &&& propagation)).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have load_full := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 full) full.toNat rfl fullSlot fullRead
    have load_propagation := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 propagation) propagation.toNat rfl propagationSlot propagationRead
    have ones : CIL.evalIntrinsic (.vector (.ones 128)) [] = some (.v128 (~~~0)) := by rfl
    repeat' first
      | exact done
      | (apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
         first
         | exact load_full _ _
         | exact load_propagation _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, checkedIntrinsic, step, cil_guard, observerCount, enabled, pureArity, scalars, CIL.step.eq_def,
               CIL.Intrinsic.available, ones, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_adv_extract, incoming128_arm_low,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_extra_mask

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector CIL.Vector

/-- Both extra-propagation stores, preserving all earlier private snapshots. -/
theorem vector128_arm_extra_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode))
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)  (baseSpecs : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)  (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
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
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run program fuel method 133 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 122 args frame [] current = .ok (final, returned) ∧ post final returned := by
  have actualResult : frame.locals[11]? = some (.bytes .vector128 resultHome) := by simpa [layout] using resultSlot
  have actualPropagation : frame.locals[20]? = some (.bytes .vector128 propagationHome) := by simpa [layout] using propagationSlot
  apply vector128_arm_full_mask program body method specs found code repairSpecs enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority result resultHome actualResult resultRead post
  intro fullHome middle fullSlot fullRead preserved middleCall middleAuthority firstWrite
  have fullTail : slots[20]? = some (.bytes .vector128 fullHome) := by simpa [layout] using fullSlot
  have savedPropagation := vector128_prior_read specs entered current middle boundary slots homes 19 20 (by decide)
    propagationHome fullHome propagationSlot fullTail _ _ firstWrite propagationRead
  apply vector128_arm_extra_mask program body method specs found code repairSpecs enabled boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority (full128 result) fullHome fullSlot fullRead
    propagation propagationHome actualPropagation savedPropagation post
  intro extraHome after extraSlot extraRead kept afterCall afterAuthority secondWrite
  have extraTail : slots[21]? = some (.bytes .vector128 extraHome) := by simpa [layout] using extraSlot
  have savedFull := vector128_prior_read specs entered middle after boundary slots homes 20 21 (by decide)
    fullHome extraHome fullTail extraTail _ _ secondWrite fullRead
  have earlier : ∀ i, i < 20 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read specs entered middle after boundary slots homes i 21 (by omega)
      reference extraHome slot extraTail _ _ secondWrite
      (vector128_prior_read specs entered current middle boundary slots homes i 20 bound
        reference fullHome slot fullTail _ _ firstWrite loaded)
  exact continuation fullHome extraHome after fullTail extraTail savedFull extraRead earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_arm_extra_pair
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector CIL.Vector

/-- Check the repair OR or high-result subtraction, including an initialized readback when the subtraction overwrites its existing private home. -/
theorem vector128_arm_repair_value (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 113 (armRepairCode))
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)  (baseSpecs : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)  (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
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
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (if subtract then corrected128 left right else left ||| right).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method (if subtract then 149 else 137) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (if subtract then 145 else 133) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [body.profile] at enabled
  |
    have specified : specs[if subtract then 10 else 22]? = some vector128ZeroSpec := by
      cases subtract <;> exact (by first | exact repairSpecs 3 | exact baseSpecs 10)
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority _ vector128ZeroSpec specified
        (.v128 (if subtract then corrected128 left right else left ||| right))
        (if subtract then corrected128 left right else left ||| right).toNat rfl
    have actual : frame.locals[if subtract then 11 else 23]? = some (.bytes .vector128 reference) := by
      cases subtract <;> exact slot
    have done := continuation reference after actual loaded retained afterCall afterAuthority written
    have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 left) left.toNat rfl leftSlot leftRead
    have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 right) right.toNat rfl rightSlot rightRead
    cases subtract <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadLeft loadRight done ⊢
    all_goals
      repeat' first
        | exact done
        | (apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
           first
           | exact loadLeft _ _
           | exact loadRight _ _
           | exact stored _ _ _
           | (simp (config := { implicitDefEqProofs := false })
               [localResult, checkedIntrinsic, step, cil_guard, observerCount, enabled, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
                 CIL.Vector.intrinsic_sub128, CIL.Vector.intrinsic_or128, corrected128,
                 checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
              first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_repair_value
end UInt256Proof.Add.Safety
