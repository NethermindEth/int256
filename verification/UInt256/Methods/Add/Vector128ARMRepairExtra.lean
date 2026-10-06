import UInt256.Methods.Add.Vector128RepairDispatch

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- ARM reuses the saved sum-only condition or extracts the two propagation
    lanes, depending on the reporting flag, then initializes repair local20. -/
theorem vector128_arm_repair_mask (enabled : Extracted.profile.advSimd = true) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (argument : args[3]? = some (.scalar (.i32 flag)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[12]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[13]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (conditionHome : Reference)
    (conditionSlot : frame.locals[14]? = some (.bytes .vector128 conditionHome))
    (conditionRead : read current conditionHome 16 1 = .ok
      (numberBytes (selectedPropagation128 flag low high).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[20]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (incoming128High low high).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (incoming128High low high).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 122 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 113 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 19 vector128ZeroSpec (by rfl)
        (.v128 (incoming128High low high)) (incoming128High low high).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
    have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 high) high.toNat rfl highSlot highRead
    have loadCondition := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 (selectedPropagation128 flag low high)) (selectedPropagation128 flag low high).toNat
      rfl conditionSlot conditionRead
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    have profile : vector128Body.profile = Extracted.profile := by rfl
    by_cases zero : flag = BitVec.ofNat 32 0
    all_goals
      simp only [selectedPropagation128, enabled, zero, and_true, and_false, ite_true, ite_false,
        true_and] at loadCondition
      repeat' first
        | exact done
        | (simp (config := { failIfUnchanged := false })
             [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero]
           apply run_next_exists post found (by rfl)
           first
           | exact loadCondition _ _
           | exact loadLow _ _
           | exact loadHigh _ _
           | exact stored _ _ _
           | (simp (config := { implicitDefEqProofs := false })
               [step, profile, enabled, cil_code, argument, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
                 CIL.Intrinsic.available, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_adv_extract,
                 incoming128_arm_high, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero,
                 checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
              first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_repair_mask
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def full128 (result : BitVec 128) : BitVec 128 :=
  CIL.Vector.zip128 (fun x y => CIL.Vector.mask64 (x == y)) result (~~~0)

theorem vector128_arm_full_mask (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (result : BitVec 128) (resultHome : Reference)
    (resultSlot : frame.locals[11]? = some (.bytes .vector128 resultHome))
    (resultRead : read current resultHome 16 1 = .ok (numberBytes result.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[21]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (full128 result).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (full128 result).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 126 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 122 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 20 vector128ZeroSpec (by rfl)
        (.v128 (full128 result)) (full128 result).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have load_result := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 result) result.toNat rfl resultSlot resultRead
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    have profile : vector128Body.profile = Extracted.profile := by rfl
    have ones : CIL.evalIntrinsic (.vector (.ones 128)) [] = some (.v128 (~~~0)) := by rfl
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact load_result _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, enabled, cil_code, pureArity, scalars, CIL.step,
               CIL.Intrinsic.available, ones, CIL.Vector.intrinsic_eq128, full128,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_full_mask

theorem vector128_arm_extra_mask (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
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
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (incoming128Low (full &&& propagation)).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 133 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 126 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 21 vector128ZeroSpec (by rfl)
        (.v128 (incoming128Low (full &&& propagation))) (incoming128Low (full &&& propagation)).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have load_full := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 full) full.toNat rfl fullSlot fullRead
    have load_propagation := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 propagation) propagation.toNat rfl propagationSlot propagationRead
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    have profile : vector128Body.profile = Extracted.profile := by rfl
    have ones : CIL.evalIntrinsic (.vector (.ones 128)) [] = some (.v128 (~~~0)) := by rfl
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact load_full _ _
         | exact load_propagation _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, enabled, cil_code, pureArity, scalars, CIL.step,
               CIL.Intrinsic.available, ones, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_adv_extract, incoming128_arm_low,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_extra_mask

end UInt256Proof.Add.Safety
