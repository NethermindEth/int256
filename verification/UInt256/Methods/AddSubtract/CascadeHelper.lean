import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.AddSubtract
open CIL.Safety

/-- A private `propagated + 2 * generated` helper with no locals. -/
def accumulateBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .const32 2, .arg 1, .mul, .add, .ret] }

/-- The helper returns the cascade sum and leaves memory unchanged. -/
theorem accumulate_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (accumulateBody profile)) (memory : Memory) (propagated generated : BitVec 32) :
    invoke program 6 index [.scalar (.i32 propagated), .scalar (.i32 generated)] memory =
      .ok (memory, [.scalar (.i32 (propagated + 2 * generated))]) := by
  simp only [invoke, found]
  change run program 6 index 0 [.scalar (.i32 propagated), .scalar (.i32 generated)]
    ⟨memory.nextIdentity, [], [], []⟩ [] memory = _
  iterate 5
    apply Eq.trans
    · apply run_next found
      · rfl
      · rfl
  rw [run]
  simp only [found]
  rfl

/-- A call to a helper that returns without touching memory continues at the next instruction. -/
theorem run_pure_call_exists {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest returned : List Value} {frame : Frame} {memory : Memory}
    (post : Memory → List Value → Prop)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest memory))
    (child : ∃ fuel, invoke program fuel callee arguments memory = .ok (memory, returned))
    (continuation : ∃ fuel result values,
      run program fuel method (pc + 1) args frame (returned ++ rest) memory = .ok (result, values) ∧
        post result values) :
    ∃ fuel result values,
      run program fuel method pc args frame stack memory = .ok (result, values) ∧ post result values := by
  obtain ⟨fuel, result, values, ran, satisfied⟩ := continuation
  obtain ⟨total, composed⟩ := run_call_exists found fetched stepped child ⟨fuel, ran⟩
  exact ⟨total, result, values, composed, satisfied⟩

#print axioms accumulate_invoke
#print axioms run_pure_call_exists
end UInt256Proof.AddSubtract
