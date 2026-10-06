import CIL.ProfileEquivalence
import CIL.Safety.Execution

namespace CIL.Safety

theorem enterFrame_profile (body : CIL.Method) (profile : CIL.FeatureProfile)
    (args : List Value) (memory : Memory) :
    enterFrame { body with profile } args memory = enterFrame body args memory := rfl

theorem step_profile_eq (body : CIL.Method) (op : CIL.Op) (p q : CIL.FeatureProfile)
    (agreement : op.ProfileAgreement p q) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) :
    step { body with profile := p } op pc args frame stack memory =
      step { body with profile := q } op pc args frame stack memory := by
  unfold step
  split <;> try rfl
  all_goals simp only [CIL.step_profile_eq op p q agreement]

theorem run_reprofile_eq (program : CIL.Program) (p q : CIL.FeatureProfile)
    (agreement : program.ProfileAgreement p q) (fuel method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) :
    run (CIL.reprofile program p) fuel method pc args frame stack memory =
      run (CIL.reprofile program q) fuel method pc args frame stack memory := by
  induction fuel generalizing method pc args frame stack memory with
  | zero => rfl
  | succ fuel ih =>
    cases hb : program[method]? with
    | none => simp [run, hb]
    | some body =>
      cases ho : body.code[pc]? with
      | none => simp [run, hb, ho]
      | some op =>
        have same := step_profile_eq body op p q
          (agreement body (List.mem_of_getElem? hb) op (List.mem_of_getElem? ho))
          pc args frame stack memory
        simp only [run, CIL.reprofile_lookup, hb, Option.map_some, ho]
        rw [same]
        cases haction : step { body with profile := q } op pc args frame stack memory with
        | error fault => rfl
        | ok action =>
          cases action with
          | next target values frame memory =>
            simpa only [Except.mapError, Bind.bind, Except.bind] using
              ih method target args frame values memory
          | returned values memory => rfl
          | call callee arguments rest memory =>
            cases child : program[callee]? with
            | none => simp [Except.mapError, Bind.bind, Except.bind, child]
            | some childBody =>
              simp only [Except.mapError, Bind.bind, Except.bind, child, Option.map_some,
                enterFrame_profile]
              simp only [ih]
          | construct callee arguments rest frame temporary memory =>
            cases child : program[callee]? with
            | none => simp [Except.mapError, Bind.bind, Except.bind, child]
            | some childBody =>
              simp only [Except.mapError, Bind.bind, Except.bind, child, Option.map_some,
                enterFrame_profile]
              simp only [ih]

theorem invoke_reprofile_eq (program : CIL.Program) (p q : CIL.FeatureProfile)
    (agreement : program.ProfileAgreement p q) (fuel method : Nat)
    (args : List Value) (memory : Memory) :
    invoke (CIL.reprofile program p) fuel method args memory =
      invoke (CIL.reprofile program q) fuel method args memory := by
  cases hb : program[method]? with
  | none => simp [invoke, hb]
  | some body =>
    simp only [invoke, CIL.reprofile_lookup, hb, Option.map_some, enterFrame_profile]
    simp only [run_reprofile_eq program p q agreement]

theorem invoke_uniform_reprofile_eq (program : CIL.Program) (p q : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p)
    (agreement : program.ProfileAgreement p q) (fuel method : Nat)
    (args : List Value) (memory : Memory) :
    invoke program fuel method args memory =
      invoke (CIL.reprofile program q) fuel method args memory := by
  have same := invoke_reprofile_eq program p q agreement fuel method args memory
  rw [CIL.reprofile_eq_of_uniform program p uniform] at same
  exact same

#print axioms invoke_reprofile_eq
#print axioms invoke_uniform_reprofile_eq
#print axioms run_reprofile_eq
#print axioms enterFrame_profile
#print axioms step_profile_eq
end CIL.Safety
