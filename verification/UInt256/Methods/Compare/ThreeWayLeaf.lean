import CIL.SymbolicExecution
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition

namespace UInt256Proof.Compare.ThreeWayLeaf
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 24 8,
  .arg 1,
  .fieldAt 24 8,
  .beq 14,
  .arg 0,
  .fieldAt 24 8,
  .arg 1,
  .fieldAt 24 8,
  .bltu 12,
  .const32 1,
  .ret,
  .const32 (BitVec.ofInt 32 (-1)),
  .ret,
  .arg 0,
  .fieldAt 16 8,
  .arg 1,
  .fieldAt 16 8,
  .beq 28,
  .arg 0,
  .fieldAt 16 8,
  .arg 1,
  .fieldAt 16 8,
  .bltu 26,
  .const32 1,
  .ret,
  .const32 (BitVec.ofInt 32 (-1)),
  .ret,
  .arg 0,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 8 8,
  .beq 42,
  .arg 0,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 8 8,
  .bltu 40,
  .const32 1,
  .ret,
  .const32 (BitVec.ofInt 32 (-1)),
  .ret,
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .fieldAt 0 8,
  .beq 56,
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .fieldAt 0 8,
  .bltu 54,
  .const32 1,
  .ret,
  .const32 (BitVec.ofInt 32 (-1)),
  .ret,
  .const32 0,
  .ret] }
def threeWayResult (memory : Memory) (left right : Reference) : BitVec 32 :=
  if inputLimb memory left 3 = inputLimb memory right 3 then
    if inputLimb memory left 2 = inputLimb memory right 2 then
      if inputLimb memory left 1 = inputLimb memory right 1 then
        if inputLimb memory left 0 = inputLimb memory right 0 then
          0
        else if (inputLimb memory left 0).toNat < (inputLimb memory right 0).toNat then -1 else 1
      else if (inputLimb memory left 1).toNat < (inputLimb memory right 1).toNat then -1 else 1
    else if (inputLimb memory left 2).toNat < (inputLimb memory right 2).toNat then -1 else 1
  else if (inputLimb memory left 3).toNat < (inputLimb memory right 3).toNat then -1 else 1

private theorem equal_step (method : CIL.Method) (pc target : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (left right : BitVec 64) :
    step method (.beq target) pc args frame (.scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
      .ok (.next (if left = right then target else pc + 1) rest frame memory) := by
  rfl

private theorem less_step (method : CIL.Method) (pc target : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (left right : BitVec 64) :
    step method (.bltu target) pc args frame (.scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
      .ok (.next (if left.toNat < right.toNat then target else pc + 1) rest frame memory) := by
  rfl

macro "threeway_leaf_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · assumption
      · simp only [body]; rfl
      · first
        | (simp (config := { implicitDefEqProofs := false }) only [equal_step, less_step, $[$facts:term],*]; rfl)
        | (simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, BitVec.lt_def, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
           try (exact ⟨rfl, rfl, rfl, rfl⟩)
           done))

theorem threeWay_run (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile)) (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (threeWayResult memory left right))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hc (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := by
    rfl
  have hl0 := hl (0 : Fin 4)
  have hl1 := hl (1 : Fin 4)
  have hl2 := hl (2 : Fin 4)
  have hl3 := hl (3 : Fin 4)
  have hr0 := hr (0 : Fin 4)
  have hr1 := hr (1 : Fin 4)
  have hr2 := hr (2 : Fin 4)
  have hr3 := hr (3 : Fin 4)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at hl0 hl1 hl2 hl3 hr0 hr1 hr2 hr3
  refine ⟨64, ?_⟩
  by_cases h3 : inputLimb memory left 3 = inputLimb memory right 3
  · by_cases h2 : inputLimb memory left 2 = inputLimb memory right 2
    · by_cases h1 : inputLimb memory left 1 = inputLimb memory right 1
      · by_cases h0 : inputLimb memory left 0 = inputLimb memory right 0
        · threeway_leaf_steps 21 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, h3, h2, h1, h0
          simp [run, found, body, step, checkedValue, numericValue, threeWayResult, h3, h2, h1, h0,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · by_cases lt : (inputLimb memory left 0).toNat < (inputLimb memory right 0).toNat
          all_goals
            threeway_leaf_steps 26 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, h3, h2, h1, h0, lt
            simp [run, found, body, step, checkedValue, numericValue, threeWayResult, h3, h2, h1, h0, lt,
              Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · by_cases lt : (inputLimb memory left 1).toNat < (inputLimb memory right 1).toNat
        all_goals
          threeway_leaf_steps 21 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, h3, h2, h1, lt
          simp [run, found, body, step, checkedValue, numericValue, threeWayResult, h3, h2, h1, lt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · by_cases lt : (inputLimb memory left 2).toNat < (inputLimb memory right 2).toNat
      all_goals
        threeway_leaf_steps 16 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, h3, h2, lt
        simp [run, found, body, step, checkedValue, numericValue, threeWayResult, h3, h2, lt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · by_cases lt : (inputLimb memory left 3).toNat < (inputLimb memory right 3).toNat
    all_goals
      threeway_leaf_steps 11 with fl, fr, hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, h3, lt
      simp [run, found, body, step, checkedValue, numericValue, threeWayResult, h3, lt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms threeWay_run
end UInt256Proof.Compare.ThreeWayLeaf
