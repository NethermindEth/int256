import UInt256.Methods.AddSubtract.Vector128Prefix
import CIL.SIMD.EvaluationLemmas
import CIL.SIMD.Incoming128

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety CIL.Vector

def incoming128Offset : Nat :=
  (vector128Body.code.findIdx fun op => match op with
    | .feature .advSimd => true | _ => false) - 37

def incoming128Start (upper : Bool) : Nat :=
  incoming128Offset + (if Extracted.profile.advSimd then (if upper then 44 else 39) else (if upper then 54 else 50))

def incoming128End (upper : Bool) : Nat :=
  incoming128Offset + (if Extracted.profile.advSimd then (if upper then 49 else 44) else (if upper then 62 else 54))

/-- Follow the selected ISA's actual incoming-mask instructions and initialize
    its private slot. Both ISAs produce the same explicit lane arrangement. -/
theorem vector128_incoming_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high : BitVec 128) (stack : List Value) (lowHome highHome : Reference)
    (lowSlot : frame.locals[6 + incoming128Offset]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[7 + incoming128Offset]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[(if upper then 9 else 8) + incoming128Offset]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok
        (numberBytes (if upper then incoming128High low high else incoming128Low low).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference
        (numberBytes (if upper then incoming128High low high else incoming128Low low).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (incoming128End upper) args frame
          stack after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (incoming128Start upper) args frame
        stack current = .ok (result, returned) ∧ post result returned := by
  have specified : vector128Specs[(if upper then 8 else 7) + incoming128Offset]? = some vector128ZeroSpec := by
    cases upper <;> rfl
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (if upper then incoming128High low high else incoming128Low low))
      (if upper then incoming128High low high else incoming128Low low).toNat rfl
  have actual : frame.locals[(if upper then 9 else 8) + incoming128Offset]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  conv at lowSlot in incoming128Offset => cbv
  conv at highSlot in incoming128Offset => cbv
  simp only [incoming128Offset] at stored
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored done ⊢
  all_goals
    conv at done in incoming128End => cbv
    conv in incoming128Start => cbv
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_adv_extract,
               CIL.Vector.intrinsic_sse_shift, CIL.Vector.intrinsic_sse_align,
               CIL.Vector.intrinsic_reinterpret128, incoming128_arm_low, incoming128_arm_high,
               incoming128_sse_low, incoming128_sse_high, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- The feature guard and ARM-only final jump follow the selected extraction. -/
theorem vector128_incoming_dispatch (memory : Memory) (frame : Frame) (args stack : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (incoming128Start false) args frame stack memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (37 + incoming128Offset) args frame stack memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  conv at continuation in incoming128Start => cbv
  conv in incoming128Offset => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem vector128_incoming_join (memory : Memory) (frame : Frame) (args stack : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (62 + incoming128Offset) args frame stack memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (incoming128End true) args frame stack memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  conv in incoming128End => cbv
  conv at continuation in incoming128Offset => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, pureArity, scalars, CIL.step, checkedValue, numericValue,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)


#print axioms vector128_incoming_checked
#print axioms vector128_incoming_dispatch
#print axioms vector128_incoming_join
end UInt256Proof.AddSubtract.Safety
