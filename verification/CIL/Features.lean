import Std

/- .NET runtime capability references (model scope .NET 10):
https://learn.microsoft.com/dotnet/standard/simd
https://github.com/dotnet/runtime/blob/v10.0.0/docs/design/features/hw-intrinsics.md
https://github.com/dotnet/runtime/blob/v10.0.0/docs/design/coreclr/botr/vectors-and-intrinsics.md
IsSupported is a runtime capability, including OS support and runtime disabling;
it is not just a CPUID bit. Operation prerequisites are retained explicitly.
The inherited x86 chain in this model is SSE2 <- SSSE3 <- SSE4.2 <- AVX
<- AVX2 <- AVX512F. AVX512F.VL additionally requires AVX512F; the reverse
implication is not valid. BMI1 is independent of this chain.
https://learn.microsoft.com/dotnet/api/system.runtime.intrinsics.x86.avx512f?view=net-10.0
https://devblogs.microsoft.com/dotnet/hardware-intrinsics-in-net-core/ -/

namespace CIL

inductive Feature where
  | advSimd | sse2 | ssse3 | sse42 | avx | avx2 | avx512F | avx512FVL | bmi1
  deriving DecidableEq, Repr

inductive Architecture where
  | scalar | arm64 | x64
  deriving DecidableEq, Repr

/-- Runtime-visible flags are fixed throughout an execution. Runtime disabling is
represented by false flags; BMI1 is independent of the AVX selection. -/
structure FeatureProfile where
  architecture : Architecture := .scalar
  nativeWidth : Nat := 64
  littleEndian : Bool := true
  advSimd : Bool := false
  sse2 : Bool := false
  ssse3 : Bool := false
  sse42 : Bool := false
  avx : Bool := false
  avx2 : Bool := false
  avx512F : Bool := false
  avx512FVL : Bool := false
  bmi1 : Bool := false
  deriving DecidableEq, Repr

def FeatureProfile.scalar : FeatureProfile := {}

def FeatureProfile.evaluate (p : FeatureProfile) : Feature → Bool
  | .advSimd => p.advSimd
  | .sse2 => p.sse2
  | .ssse3 => p.ssse3
  | .sse42 => p.sse42
  | .avx => p.avx
  | .avx2 => p.avx2
  | .avx512F => p.avx512F
  | .avx512FVL => p.avx512FVL
  | .bmi1 => p.bmi1

/-- Declared capability domain: 64-bit little-endian execution, architecture
separation, and prerequisites used by the reachable SSE/AVX operations. This is
an explicit domain, rather than a claim to enumerate every possible CLR host. -/
def FeatureProfile.Valid (p : FeatureProfile) : Prop :=
  p.nativeWidth = 64 ∧ p.littleEndian = true ∧
  (p.advSimd = true → p.architecture = .arm64) ∧
  ((p.sse2 || p.ssse3 || p.sse42 || p.avx || p.avx2 || p.avx512F || p.avx512FVL || p.bmi1) = true →
    p.architecture = .x64) ∧
  (p.ssse3 = true → p.sse2 = true) ∧
  (p.sse42 = true → p.sse2 = true ∧ p.ssse3 = true) ∧
  (p.avx2 = true → p.avx = true) ∧
  (p.avx512FVL = true → p.avx512F = true) ∧
  (p.avx = true → p.sse42 = true) ∧
  (p.avx512F = true → p.avx2 = true)

instance (p : FeatureProfile) : Decidable p.Valid := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem FeatureProfile.scalar_evaluate (f : Feature) : scalar.evaluate f = false := by
  cases f <;> rfl

theorem FeatureProfile.scalar_valid : scalar.Valid := by decide

theorem FeatureProfile.avx512F_implies_avx2 (p : FeatureProfile) (h : p.Valid)
    (hf : p.avx512F = true) : p.avx2 = true := h.2.2.2.2.2.2.2.2.2 hf

theorem FeatureProfile.avx512FVL_implies_avx2 (p : FeatureProfile) (h : p.Valid)
    (hvl : p.avx512FVL = true) : p.avx2 = true :=
  p.avx512F_implies_avx2 h (h.2.2.2.2.2.2.2.1 hvl)

/-- The finite branch distinctions currently queried by production Add/Subtract.
This classifier supplies feature evidence only, not an arithmetic proof. -/
structure FeatureBehaviour where
  avx2 : Bool
  advSimd : Bool
  sse42 : Bool
  avx512FVL : Bool
  bmi1 : Bool
  deriving DecidableEq, Repr

def FeatureProfile.behaviour (p : FeatureProfile) : FeatureBehaviour :=
  ⟨p.avx2, p.advSimd, p.sse42, p.avx512FVL, p.bmi1⟩

def Feature.productionQueries : List Feature := [.avx2, .advSimd, .sse42, .avx512FVL, .bmi1]

theorem FeatureProfile.same_behaviour_queries (p q : FeatureProfile)
    (h : p.behaviour = q.behaviour) (f : Feature) (hf : f ∈ Feature.productionQueries) :
    p.evaluate f = q.evaluate f := by
  cases f <;> simp [Feature.productionQueries] at hf
  · exact congrArg FeatureBehaviour.advSimd h
  · exact congrArg FeatureBehaviour.sse42 h
  · exact congrArg FeatureBehaviour.avx2 h
  · exact congrArg FeatureBehaviour.avx512FVL h
  · exact congrArg FeatureBehaviour.bmi1 h

inductive FeatureClass where
  | scalar | arm64 | sse
  | avx2 (bmi1 : Bool)
  | avx512 (bmi1 : Bool)
  deriving DecidableEq, Repr

def FeatureClass.all : List FeatureClass :=
  [.scalar, .arm64, .sse, .avx2 false, .avx2 true, .avx512 false, .avx512 true]

def FeatureProfile.classify (p : FeatureProfile) : FeatureClass :=
  if p.avx2 then
    if p.avx512FVL then .avx512 p.bmi1 else .avx2 p.bmi1
  else if p.advSimd then .arm64 else if p.sse42 then .sse else .scalar

def FeatureClass.representative : FeatureClass → FeatureProfile
  | .scalar => .scalar
  | .arm64 => { architecture := .arm64, advSimd := true }
  | .sse => { architecture := .x64, sse2 := true, ssse3 := true, sse42 := true }
  | .avx2 bmi => { architecture := .x64, sse2 := true, ssse3 := true, sse42 := true, avx := true, avx2 := true, bmi1 := bmi }
  | .avx512 bmi => { architecture := .x64, sse2 := true, ssse3 := true, sse42 := true, avx := true, avx2 := true, avx512F := true, avx512FVL := true, bmi1 := bmi }

/-- Getter distinctions encountered on the selected family, including queries
inside helpers. BMI1 distinguishes subtraction only; addition can share it.
Extraction still needs to establish that its actual queried getters belong to
this list before this classification can justify reuse of an execution proof. -/
def FeatureClass.queries : FeatureClass → List Feature
  | .scalar => [.avx2, .advSimd, .sse42, .avx512F, .avx512FVL]
  | .sse => [.avx2, .advSimd, .sse42, .sse2, .ssse3, .avx512F, .avx512FVL]
  | .arm64 => [.avx2, .advSimd, .avx512F, .avx512FVL]
  | .avx2 _ => [.avx2, .avx512FVL, .bmi1, .avx, .sse42, .ssse3, .sse2]
  | .avx512 _ => [.avx2, .avx512FVL, .bmi1, .avx, .sse42, .ssse3, .sse2, .avx512F]

theorem FeatureProfile.classification_total (p : FeatureProfile) :
    p.classify ∈ FeatureClass.all := by
  cases ha : p.avx2
  · cases hn : p.advSimd <;> cases hs : p.sse42 <;>
      simp [FeatureProfile.classify, FeatureClass.all, ha, hn, hs]
  · cases hv : p.avx512FVL <;> cases hb : p.bmi1 <;>
      simp [FeatureProfile.classify, FeatureClass.all, ha, hv, hb]

theorem FeatureClass.representative_valid (c : FeatureClass) : c.representative.Valid := by
  cases c with
  | scalar => exact FeatureProfile.scalar_valid
  | arm64 => decide
  | sse => decide
  | avx2 bmi => cases bmi <;> decide
  | avx512 bmi => cases bmi <;> decide

theorem FeatureProfile.classification_queries (p : FeatureProfile) (h : p.Valid) (f : Feature)
    (hf : f ∈ p.classify.queries) :
    p.evaluate f = p.classify.representative.evaluate f := by
  rcases h with ⟨_, _, _, _, hss, hsse, havx, hvl, havxsse, hfavx⟩
  cases ha : p.avx2
  · cases hn : p.advSimd <;> cases hs : p.sse42 <;> cases f <;>
      simp_all [FeatureProfile.classify, FeatureClass.queries, FeatureClass.representative,
        FeatureProfile.scalar, FeatureProfile.evaluate]
  · cases hv : p.avx512FVL <;> cases f <;>
      simp_all [FeatureProfile.classify, FeatureClass.queries, FeatureClass.representative,
        FeatureProfile.evaluate]

/-- Explicit prerequisites of ISA-specific calls on each selected family. -/
def FeatureClass.required : FeatureClass → List Feature
  | .scalar => []
  | .arm64 => [.advSimd]
  | .sse => [.sse2, .ssse3]
  | .avx2 bmi => [.sse2, .ssse3, .sse42, .avx, .avx2] ++ if bmi then [.bmi1] else []
  | .avx512 bmi => [.sse2, .ssse3, .sse42, .avx, .avx2, .avx512F, .avx512FVL] ++ if bmi then [.bmi1] else []

theorem FeatureProfile.classification_required (p : FeatureProfile) (h : p.Valid)
    (f : Feature) (hf : f ∈ p.classify.required) : p.evaluate f = true := by
  rcases h with ⟨_, _, _, _, hss, hsse, havx, hvl, havxsse, hfavx⟩
  cases ha : p.avx2
  · cases hn : p.advSimd <;> cases hs : p.sse42 <;> cases f <;>
      simp_all [FeatureProfile.classify, FeatureClass.required, FeatureProfile.evaluate]
  · cases hv : p.avx512FVL <;> cases hb : p.bmi1 <;> cases f <;>
      simp_all [FeatureProfile.classify, FeatureClass.required, FeatureProfile.evaluate]

end CIL
