import UInt256.Methods.Add.Vector128Ready

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def selectedPropagation128 (flag : BitVec 32) (low high : BitVec 128) : BitVec 128 :=
  if Extracted.profile.advSimd = true ∧ flag = BitVec.ofNat 32 0 then incoming128High low high else low ||| high

/-- Follow the actual ISA/reporting choice and store the propagation condition.
    This covers both values of the reporting choice without a caller restriction. -/
theorem vector128_decision_checked (boundary : Nat) (entered current : Memory)
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
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[14]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (selectedPropagation128 flag low high).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (selectedPropagation128 flag low high).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 107 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 94 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 13 vector128ZeroSpec (by rfl)
      (.v128 (selectedPropagation128 flag low high)) (selectedPropagation128 flag low high).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  by_cases zero : flag = BitVec.ofNat 32 0
  all_goals
    simp only [selectedPropagation128, Extracted.profile, zero, and_true, and_false, ite_true, ite_false,
      Bool.false_eq_true, false_and, true_and] at stored
    repeat' first
      | exact done
      | (simp (config := { failIfUnchanged := false })
           [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero]
         apply run_next_exists post found (by rfl)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, argument, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
               CIL.Intrinsic.available, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_adv_extract,
               incoming128_arm_high, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Test only the initialized saved condition and expose both actual targets. -/
theorem vector128_decision_branch (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (condition : BitVec 128)
    (slot : frame.locals[14]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes condition.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (if condition = BitVec.ofNat 128 0 then 204 else 111)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 107 args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 condition) condition.toNat rfl slot loaded
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  by_cases zero : condition = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact load _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_equal_all128,
               show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_decision_checked
#print axioms vector128_decision_branch
end UInt256Proof.Add.Safety
