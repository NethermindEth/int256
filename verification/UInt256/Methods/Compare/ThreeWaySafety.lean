import Extracted
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def threeWayIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any (fun op => match op with | .field _ => true | _ => false) &&
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false)

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

macro "threeway_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, CIL.step, CIL.binary, CIL.truth, BitVec.lt_def, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

theorem threeWay_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel threeWayIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (threeWayResult memory left right))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hc (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := by
    rfl
  conv in threeWayIndex => cbv
  refine ⟨64, ?_⟩
  by_cases h3 : inputLimb memory left 3 = inputLimb memory right 3
  · by_cases h2 : inputLimb memory left 2 = inputLimb memory right 2
    · by_cases h1 : inputLimb memory left 1 = inputLimb memory right 1
      · by_cases h0 : inputLimb memory left 0 = inputLimb memory right 0
        · threeway_steps 21 with fl, fr, hl, hr, hc, h3, h2, h1, h0
          simp [run, cil_code, step, checkedValue, numericValue, threeWayResult, h3, h2, h1, h0,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · by_cases lt : (inputLimb memory left 0).toNat < (inputLimb memory right 0).toNat
          all_goals
            threeway_steps 26 with fl, fr, hl, hr, hc, h3, h2, h1, h0, lt
            simp [run, cil_code, step, checkedValue, numericValue, threeWayResult, h3, h2, h1, h0, lt,
              Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · by_cases lt : (inputLimb memory left 1).toNat < (inputLimb memory right 1).toNat
        all_goals
          threeway_steps 21 with fl, fr, hl, hr, hc, h3, h2, h1, lt
          simp [run, cil_code, step, checkedValue, numericValue, threeWayResult, h3, h2, h1, lt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · by_cases lt : (inputLimb memory left 2).toNat < (inputLimb memory right 2).toNat
      all_goals
        threeway_steps 16 with fl, fr, hl, hr, hc, h3, h2, lt
        simp [run, cil_code, step, checkedValue, numericValue, threeWayResult, h3, h2, lt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · by_cases lt : (inputLimb memory left 3).toNat < (inputLimb memory right 3).toNat
    all_goals
      threeway_steps 11 with fl, fr, hl, hr, hc, h3, lt
      simp [run, cil_code, step, checkedValue, numericValue, threeWayResult, h3, lt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms threeWay_run
end UInt256Proof.Compare.Safety
