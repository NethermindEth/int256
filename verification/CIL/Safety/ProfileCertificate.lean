import CIL.Safety.ProfileEquivalence
import CIL.Safety.Certificate

namespace CIL.Safety

@[simp] theorem programStaticDescriptors_reprofile (program : CIL.Program) (p : CIL.FeatureProfile) :
    programStaticDescriptors (CIL.reprofile program p) = programStaticDescriptors program := by
  simp [programStaticDescriptors, CIL.reprofile, List.flatMap_map]

/-- Rebuild the full certificate for the target profile. Prefix liveness and
returned-state validity follow from the same checked initial state and actual
execution, not from an assumption that only the final result matters. -/
theorem invocationCertificate_reprofile (program : CIL.Program) (p q : CIL.FeatureProfile)
    (agreement : program.ProfileAgreement p q) (method : Nat) (args : List Value)
    (initial : Memory) (fuel : Nat) (final : Memory) (values : List Value)
    (certificate : InvocationCertificate (CIL.reprofile program p) method args initial fuel final values) :
    InvocationCertificate (CIL.reprofile program q) method args initial fuel final values := by
  obtain ⟨_, actual, frame, entered, lookup, checked, setup, finished, live, _, _⟩ := certificate
  cases hb : program[method]? with
  | none => simp [hb] at lookup
  | some body =>
    simp only [CIL.reprofile_lookup, hb, Option.map_some, Option.some.injEq] at lookup
    subst actual
    have state : LiveState (CIL.reprofile program q) args frame [] entered :=
      { live with statics := by simpa only [programStaticDescriptors_reprofile] using live.statics }
    apply certify_invocation (CIL.reprofile program q) method { body with profile := q }
      args initial frame entered fuel final values
    · simp [hb]
    · exact checked
    · simpa only [enterFrame_profile] using setup
    · exact state
    · rw [← run_reprofile_eq program p q agreement]
      exact finished

theorem invocationCertificate_uniform_reprofile (program : CIL.Program) (p q : CIL.FeatureProfile)
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (method : Nat) (args : List Value) (initial : Memory) (fuel : Nat)
    (final : Memory) (values : List Value)
    (certificate : InvocationCertificate program method args initial fuel final values) :
    InvocationCertificate (CIL.reprofile program q) method args initial fuel final values := by
  apply invocationCertificate_reprofile program p q agreement method args initial fuel final values
  simpa only [CIL.reprofile_eq_of_uniform program p uniform] using certificate

#print axioms invocationCertificate_uniform_reprofile
#print axioms programStaticDescriptors_reprofile
#print axioms invocationCertificate_reprofile
end CIL.Safety
