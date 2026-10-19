import UInt256.Methods.AddSubtract.CascadeHelper
import CIL.SIMD.EvaluationLemmas

namespace UInt256Proof.Subtract.Profile
open CIL.Safety

/-- A private helper returning the lane-wise or of two vectors. -/
def mergePropagationBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .arg 1, .intrinsic (.vector (.bor 128)) 2, .ret] }

/-- A private AdvSimd helper extracting the 128-bit window one lane into the pair. -/
def extractPairBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .arg 1, .const32 1, .intrinsic (.advSimd .extract64) 3, .ret] }

theorem merge_propagation_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (mergePropagationBody profile)) (memory : Memory) (a b : BitVec 128) :
    invoke program 4 index [.scalar (.v128 a), .scalar (.v128 b)] memory =
      .ok (memory, [.scalar (.v128 (a ||| b))]) := by
  simp only [invoke, found]
  change run program 4 index 0 [.scalar (.v128 a), .scalar (.v128 b)]
    ⟨memory.nextIdentity, [], [], []⟩ [] memory = _
  iterate 3
    apply Eq.trans
    · apply run_next found
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
            CIL.Vector.intrinsic_or128, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  rw [run]
  simp only [found]
  rfl

theorem extract_pair_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (extractPairBody profile)) (adv : profile.advSimd = true)
    (memory : Memory) (a b : BitVec 128) :
    invoke program 5 index [.scalar (.v128 a), .scalar (.v128 b)] memory =
      .ok (memory, [.scalar (.v128 (CIL.Vector.advExtract64 a b 1))]) := by
  have bodyProfile : (extractPairBody profile).profile = profile := rfl
  simp only [invoke, found]
  change run program 5 index 0 [.scalar (.v128 a), .scalar (.v128 b)]
    ⟨memory.nextIdentity, [], [], []⟩ [] memory = _
  iterate 4
    apply Eq.trans
    · apply run_next found
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, bodyProfile, adv, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
            CIL.Vector.intrinsic_adv_extract, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure,
            Except.pure]
        try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  rw [run]
  simp only [found]
  rfl

#print axioms merge_propagation_invoke
#print axioms extract_pair_invoke
end UInt256Proof.Subtract.Profile
