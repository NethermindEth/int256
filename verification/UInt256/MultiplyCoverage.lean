import CIL.FeatureCoverage
import CIL.MultiplyFeatures

open CIL
namespace UInt256Proof

/-- The arithmetic class fixes the four arithmetic queries. Storage observes
    its own independent flag; neither family premise supplies correctness. -/
def MultiplyFamily (contract : Program → Nat → Prop) (artifact : Representative) : Prop :=
  ∀ profile : FeatureProfile, profile.Valid →
    artifact.profile.classifyMultiply = profile.classifyMultiply →
    artifact.profile.vector256Accelerated = profile.vector256Accelerated →
    contract (reprofile artifact.program profile) artifact.entry

/-- All seven arithmetic classes, each with both storage choices, are required.
    Certificates remain about each actual extracted program and public entry. -/
theorem multiply_complete_coverage (contract : Program → Nat → Prop)
    (artifacts : MultiplyClass → Bool → Representative)
    (classes : ∀ family ∈ MultiplyClass.all, ∀ storage : Bool,
      (artifacts family storage).profile.classifyMultiply = family)
    (storageFlags : ∀ family ∈ MultiplyClass.all, ∀ storage : Bool,
      (artifacts family storage).profile.vector256Accelerated = storage)
    (checked : ∀ family ∈ MultiplyClass.all, ∀ storage : Bool,
      MultiplyFamily contract (artifacts family storage))
    (profile : FeatureProfile) (valid : profile.Valid) :
    contract (reprofile (artifacts profile.classifyMultiply profile.vector256Accelerated).program profile)
      (artifacts profile.classifyMultiply profile.vector256Accelerated).entry :=
  checked profile.classifyMultiply profile.multiply_classification_total
    profile.vector256Accelerated profile valid
    (classes profile.classifyMultiply profile.multiply_classification_total _)
    (storageFlags profile.classifyMultiply profile.multiply_classification_total _)

end UInt256Proof
#print axioms UInt256Proof.multiply_complete_coverage
