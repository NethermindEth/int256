import UInt256.Methods.Compare.Lemmas
import UInt256.Methods.Compare.WrapperSafetyContract
import UInt256.Safety.LimbAccess
import UInt256.Safety.ProfileContracts
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.SymbolicExecution

namespace CompareFixture
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare.Safety

/-- Result of the ladder that decides each limb with a strict-less then a strict-greater branch. -/
def ladderResult (memory : Memory) (left right : Reference) : BitVec 32 :=
  if inputLimb memory left 3 < inputLimb memory right 3 then 1
  else if inputLimb memory right 3 < inputLimb memory left 3 then 0
  else if inputLimb memory left 2 < inputLimb memory right 2 then 1
  else if inputLimb memory right 2 < inputLimb memory left 2 then 0
  else if inputLimb memory left 1 < inputLimb memory right 1 then 1
  else if inputLimb memory right 1 < inputLimb memory left 1 then 0
  else if inputLimb memory left 0 < inputLimb memory right 0 then 1 else 0

macro "ladder_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| cil_checked_steps $count [readOnlyArguments, $facts:term,*])

theorem ladder_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel wrapperLeafIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (ladderResult memory left right))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hl0 := hl (0 : Fin 4)
  have hl1 := hl (1 : Fin 4)
  have hl2 := hl (2 : Fin 4)
  have hl3 := hl (3 : Fin 4)
  have hr0 := hr (0 : Fin 4)
  have hr1 := hr (1 : Fin 4)
  have hr2 := hr (2 : Fin 4)
  have hr3 := hr (3 : Fin 4)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at hl0 hl1 hl2 hl3 hr0 hr1 hr2 hr3
  have k0 : instruction (.const32 0#32) [] memory = .ok (memory, [.scalar (.i32 0#32)]) := rfl
  have k1 : instruction (.const32 1#32) [] memory = .ok (memory, [.scalar (.i32 1#32)]) := rfl
  conv in wrapperLeafIndex => cbv
  refine ⟨48, ?_⟩
  by_cases a3 : inputLimb memory left 3 < inputLimb memory right 3
  · have a3c := BitVec.not_le.mpr a3
    rw [show ladderResult memory left right = 1 by simp [ladderResult, a3]]
    ladder_steps 6 with k0, k1, fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, a3, a3c
    simp [run, cil_code, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have a3c := BitVec.not_lt.mp a3
    by_cases b3 : inputLimb memory right 3 < inputLimb memory left 3
    · have b3c := BitVec.not_le.mpr b3
      rw [show ladderResult memory left right = 0 by simp [ladderResult, a3, b3]]
      ladder_steps 11 with k0, k1, fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, a3, a3c, b3, b3c
      simp [run, cil_code, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · have b3c := BitVec.not_lt.mp b3
      by_cases a2 : inputLimb memory left 2 < inputLimb memory right 2
      · have a2c := BitVec.not_le.mpr a2
        rw [show ladderResult memory left right = 1 by simp [ladderResult, a3, b3, a2]]
        ladder_steps 16 with k0, k1, fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, a3, a3c, b3, b3c, a2, a2c
        simp [run, cil_code, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · have a2c := BitVec.not_lt.mp a2
        by_cases b2 : inputLimb memory right 2 < inputLimb memory left 2
        · have b2c := BitVec.not_le.mpr b2
          rw [show ladderResult memory left right = 0 by simp [ladderResult, a3, b3, a2, b2]]
          ladder_steps 21 with k0, k1, fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, a3, a3c, b3, b3c, a2, a2c, b2, b2c
          simp [run, cil_code, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · have b2c := BitVec.not_lt.mp b2
          by_cases a1 : inputLimb memory left 1 < inputLimb memory right 1
          · have a1c := BitVec.not_le.mpr a1
            rw [show ladderResult memory left right = 1 by simp [ladderResult, a3, b3, a2, b2, a1]]
            ladder_steps 26 with k0, k1, fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, a3, a3c, b3, b3c, a2, a2c, b2, b2c, a1, a1c
            simp [run, cil_code, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
              Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          · have a1c := BitVec.not_lt.mp a1
            by_cases b1 : inputLimb memory right 1 < inputLimb memory left 1
            · have b1c := BitVec.not_le.mpr b1
              rw [show ladderResult memory left right = 0 by simp [ladderResult, a3, b3, a2, b2, a1, b1]]
              ladder_steps 31 with k0, k1, fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, a3, a3c, b3, b3c, a2, a2c, b2, b2c, a1, a1c, b1, b1c
              simp [run, cil_code, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
                Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            · have b1c := BitVec.not_lt.mp b1
              rw [show ladderResult memory left right = (if inputLimb memory left 0 < inputLimb memory right 0 then 1 else 0) by simp [ladderResult, a3, b3, a2, b2, a1, b1]]
              ladder_steps 35 with k0, k1, fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, a3, a3c, b3, b3c, a2, a2c, b2, b2c, a1, a1c, b1, b1c
              simp [run, cil_code, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend,
                Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)

#print axioms ladder_run

theorem limb_ladder {α : Type} (x y : BitVec 64) (less greater equal : α) :
    (if x < y then less else if y < x then greater else equal) =
      if x = y then equal else if x < y then less else greater := by
  by_cases same : x = y
  · subst same
    simp
  · have distinct : x.toNat ≠ y.toNat := fun h => same (BitVec.eq_of_toNat_eq h)
    by_cases below : x < y
    · simp [same, below]
    · have above : y < x := by simp only [BitVec.lt_def] at *; omega
      simp [same, below, above]

theorem ladder_result_math (memory : Memory) (left right : Reference) :
    ladderResult memory left right =
      if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  clear leftValue rightValue
  simp only [UInt256Proof.Compare.value_lt_descending]
  unfold ladderResult
  simp only [limb_ladder]
  by_cases h3 : inputLimb memory left 3 = inputLimb memory right 3 <;>
    by_cases h2 : inputLimb memory left 2 = inputLimb memory right 2 <;>
    by_cases h1 : inputLimb memory left 1 = inputLimb memory right 1 <;>
    simp [h3, h2, h1]

def ladderBody : CIL.Method := Extracted.program[wrapperLeafIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem ladder_checked : BinaryReadOnlyInvocation lessValue Extracted.program wrapperLeafIndex := by
  intro memory left right call
  exact certify_readOnly_binary Extracted.program wrapperLeafIndex ladderBody
    (fun left right => .i32 (if left.toNat < right.toNat then 1 else 0)) (by rfl)
    (by
      intro left right
      conv in ladderBody => cbv
      simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit])
    (fun memory left right frame call => by
      simpa only [ladder_result_math] using ladder_run memory left right frame call)
    memory left right call

#print axioms limb_ladder
#print axioms ladder_result_math
#print axioms ladder_checked
end CompareFixture

open UInt256Model.Safety UInt256Proof.Compare.Safety in
/-- Scalar-path comparison decided by a strict-less then strict-greater branch per limb. -/
theorem CompareFixture.correct :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  have entry : BinaryReadOnlyInvocation lessValue Extracted.program Extracted.entryIndex :=
    entry_checked CompareFixture.ladder_checked
  simpa only [lessValue] using entry.to_contract

#print axioms CompareFixture.correct
