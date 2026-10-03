import CIL.ProfileEquivalence

namespace CIL

/-- All capability choices are finite. This key does not assign algorithm contracts. -/
structure ProfileKey where
  architecture : Architecture
  bits : BitVec 15
  deriving DecidableEq, Repr

def FeatureProfile.key (p : FeatureProfile) : ProfileKey :=
  ⟨p.architecture, ((((((((((((((BitVec.ofBool p.vector256Accelerated ++ BitVec.ofBool p.armBase64) ++ BitVec.ofBool p.bmi2) ++ BitVec.ofBool p.avx512DQVL) ++ BitVec.ofBool p.avx512DQ) ++ BitVec.ofBool p.sse41) ++ BitVec.ofBool p.bmi1) ++ BitVec.ofBool p.avx512FVL) ++ BitVec.ofBool p.avx512F) ++ BitVec.ofBool p.avx2) ++ BitVec.ofBool p.avx) ++ BitVec.ofBool p.sse42) ++ BitVec.ofBool p.ssse3) ++ BitVec.ofBool p.sse2) ++ BitVec.ofBool p.advSimd)⟩

def ProfileKey.profile (key : ProfileKey) : FeatureProfile :=
  { architecture := key.architecture
    advSimd := key.bits.getLsbD 0
    sse2 := key.bits.getLsbD 1
    ssse3 := key.bits.getLsbD 2
    sse42 := key.bits.getLsbD 3
    avx := key.bits.getLsbD 4
    avx2 := key.bits.getLsbD 5
    avx512F := key.bits.getLsbD 6
    avx512FVL := key.bits.getLsbD 7
    bmi1 := key.bits.getLsbD 8
    sse41 := key.bits.getLsbD 9
    avx512DQ := key.bits.getLsbD 10
    avx512DQVL := key.bits.getLsbD 11
    bmi2 := key.bits.getLsbD 12
    armBase64 := key.bits.getLsbD 13
    vector256Accelerated := key.bits.getLsbD 14
  }

def ProfileKey.all : List ProfileKey :=
  [.scalar, .arm64, .x64].flatMap fun architecture =>
    List.ofFn fun bits : Fin (2^15) => ⟨architecture, BitVec.ofFin bits⟩

theorem ProfileKey.mem_all (key : ProfileKey) : key ∈ ProfileKey.all := by
  apply List.mem_flatMap.mpr
  refine ⟨key.architecture, ?_, List.mem_ofFn.mpr ⟨key.bits.toFin, ?_⟩⟩
  · cases key.architecture <;> simp
  · simp

theorem FeatureProfile.key_profile (p : FeatureProfile) (h : p.Valid) : p.key.profile = p := by
  have hw := h.1
  have he := h.2.1
  cases p
  dsimp only at hw he
  simp only [FeatureProfile.key, ProfileKey.profile, hw, he, FeatureProfile.mk.injEq]
  simp only [BitVec.getLsbD_append]
  simp

/-- Includes every valid declared profile, including independent BMI and portable
acceleration choices. Per-operation representative proofs remain separate. -/
def FeatureProfile.allValid : List FeatureProfile :=
  (ProfileKey.all.map ProfileKey.profile).filter fun profile => decide profile.Valid

theorem FeatureProfile.mem_allValid (p : FeatureProfile) (h : p.Valid) :
    p ∈ FeatureProfile.allValid := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨p.key, p.key.mem_all, p.key_profile h⟩, ?_⟩
  simp [h]

structure Representative where
  program : Program
  profile : FeatureProfile
  entry : Nat

def Representative.Agrees (representative : Representative) (profile : FeatureProfile) : Prop :=
  (∀ body ∈ representative.program, body.profile = representative.profile) ∧
  representative.program.ProfileAgreement representative.profile profile

def Representative.GroupCovered (representatives : List Representative) : Prop :=
  ∀ profile, profile.Valid → ∃ representative ∈ representatives, representative.Agrees profile

def Representative.GroupChecked (contract : Program → Nat → Prop)
    (representatives : List Representative) : Prop :=
  ∀ representative ∈ representatives, contract representative.program representative.entry

/-- Coverage transfers the exact selected contract only when a checked operation
contract supplies its own execution-preserving transport theorem. -/
theorem Representative.group_contract (contract : Program → Nat → Prop)
    (representatives : List Representative)
    (covered : Representative.GroupCovered representatives)
    (checked : Representative.GroupChecked contract representatives)
    (transport : ∀ program entry original selected,
      (∀ body ∈ program, body.profile = original) → program.ProfileAgreement original selected →
      contract program entry → contract (reprofile program selected) entry)
    (profile : FeatureProfile) (valid : profile.Valid) :
    ∃ representative ∈ representatives,
      representative.Agrees profile ∧
      contract (reprofile representative.program profile) representative.entry := by
  obtain ⟨representative, member, uniform, agreement⟩ := covered profile valid
  exact ⟨representative, member, ⟨uniform, agreement⟩,
    transport representative.program representative.entry representative.profile profile
      uniform agreement (checked representative member)⟩

#print axioms FeatureProfile.mem_allValid
#print axioms Representative.group_contract

end CIL
