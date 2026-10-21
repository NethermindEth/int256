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

private theorem checked_reference {memory : Memory} {input : Reference}
    (formed : form memory input = .ok input) :
    checkedValue memory (.reference (.address input)) = .ok (.reference (.address input)) := by
  simp only [checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

private theorem step_arg_first {method : CIL.Method} {pc : Nat} {rest stack : List Value} {frame : Frame}
    {memory : Memory} {input : Reference} (formed : form memory input = .ok input) :
    step method (.arg 0) pc (.reference (.address input) :: rest) frame stack memory =
      .ok (.next (pc + 1) (.reference (.address input) :: stack) frame memory) := by
  show (checkedValue memory (.reference (.address input))).bind _ = _
  rw [checked_reference formed]; rfl

private theorem step_arg_second {method : CIL.Method} {pc : Nat} {first : Value} {rest stack : List Value}
    {frame : Frame} {memory : Memory} {input : Reference} (formed : form memory input = .ok input) :
    step method (.arg 1) pc (first :: .reference (.address input) :: rest) frame stack memory =
      .ok (.next (pc + 1) (.reference (.address input) :: stack) frame memory) := by
  show (checkedValue memory (.reference (.address input))).bind _ = _
  rw [checked_reference formed]; rfl

private theorem step_field {method : CIL.Method} {pc offset : Nat} {args rest values : List Value}
    {frame : Frame} {memory : Memory} {reference : ManagedReference}
    (loaded : instruction (.fieldAt offset 8) (.reference reference :: rest) memory = .ok (memory, values)) :
    step method (.fieldAt offset 8) pc args frame (.reference reference :: rest) memory =
      .ok (.next (pc + 1) values frame memory) := by
  have unfolded : step method (.fieldAt offset 8) pc args frame (.reference reference :: rest) memory =
      (instruction (.fieldAt offset 8) (.reference reference :: rest) memory).bind
        fun result => .ok (.next (pc + 1) result.2 frame result.1) := rfl
  rw [unfolded, loaded]; rfl

private theorem equal_taken {method : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {left right : BitVec 64} (equal : left = right) :
    step method (.beq target) pc args frame (.scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
      .ok (.next target rest frame memory) := by
  rw [equal_step, ite_eq_left equal]

private theorem equal_skipped {method : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {left right : BitVec 64} (different : ¬left = right) :
    step method (.beq target) pc args frame (.scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := by
  rw [equal_step, ite_eq_right different]

private theorem less_taken {method : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {left right : BitVec 64} (less : left.toNat < right.toNat) :
    step method (.bltu target) pc args frame (.scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
      .ok (.next target rest frame memory) := by
  rw [less_step, ite_eq_left less]

private theorem less_skipped {method : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {left right : BitVec 64} (notLess : ¬left.toNat < right.toNat) :
    step method (.bltu target) pc args frame (.scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := by
  rw [less_step, ite_eq_right notLess]

set_option hygiene false in
/-- One instruction step; failed alternatives stay reducible so they never unfold memory. -/
macro "threeway_step" : tactic =>
  `(tactic| refine (run_next found rfl (by
      first
        | (with_reducible exact step_arg_first fl)
        | (with_reducible exact step_arg_second fr)
        | ((with_reducible apply step_field)
           first
             | with_reducible exact hl0 _ | with_reducible exact hl1 _ | with_reducible exact hl2 _
             | with_reducible exact hl3 _ | with_reducible exact hr0 _ | with_reducible exact hr1 _
             | with_reducible exact hr2 _ | with_reducible exact hr3 _)
        | ((with_reducible apply equal_taken); with_reducible assumption)
        | ((with_reducible apply equal_skipped); with_reducible assumption)
        | ((with_reducible apply less_taken); with_reducible assumption)
        | ((with_reducible apply less_skipped); with_reducible assumption)
        | rfl)).trans ?_)

set_option hygiene false in
/-- Run to the return, then select the matching result branch. -/
macro "threeway_finish" "with" facts:term,* : tactic =>
  `(tactic| (
    repeat threeway_step
    refine (run_return found rfl rfl rfl).trans ?_
    rw [threeWayResult, $[$facts:term],*]
    rfl))

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
  simp only [readOnlyArguments, List.map]
  by_cases h3 : inputLimb memory left 3 = inputLimb memory right 3
  · by_cases h2 : inputLimb memory left 2 = inputLimb memory right 2
    · by_cases h1 : inputLimb memory left 1 = inputLimb memory right 1
      · by_cases h0 : inputLimb memory left 0 = inputLimb memory right 0
        · threeway_finish with ite_eq_left h3, ite_eq_left h2, ite_eq_left h1, ite_eq_left h0
        · by_cases lt : (inputLimb memory left 0).toNat < (inputLimb memory right 0).toNat
          · threeway_finish with ite_eq_left h3, ite_eq_left h2, ite_eq_left h1, ite_eq_right h0, ite_eq_left lt
          · threeway_finish with ite_eq_left h3, ite_eq_left h2, ite_eq_left h1, ite_eq_right h0, ite_eq_right lt
      · by_cases lt : (inputLimb memory left 1).toNat < (inputLimb memory right 1).toNat
        · threeway_finish with ite_eq_left h3, ite_eq_left h2, ite_eq_right h1, ite_eq_left lt
        · threeway_finish with ite_eq_left h3, ite_eq_left h2, ite_eq_right h1, ite_eq_right lt
    · by_cases lt : (inputLimb memory left 2).toNat < (inputLimb memory right 2).toNat
      · threeway_finish with ite_eq_left h3, ite_eq_right h2, ite_eq_left lt
      · threeway_finish with ite_eq_left h3, ite_eq_right h2, ite_eq_right lt
  · by_cases lt : (inputLimb memory left 3).toNat < (inputLimb memory right 3).toNat
    · threeway_finish with ite_eq_right h3, ite_eq_left lt
    · threeway_finish with ite_eq_right h3, ite_eq_right lt

#print axioms threeWay_run
end UInt256Proof.Compare.ThreeWayLeaf
