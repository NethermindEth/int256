import UInt256.Safety.OrderedScalarContract
import UInt256.Safety.ProfileContracts

namespace UInt256Model.Safety
open CIL.Safety

theorem OrderedScalarContract.reprofile {α : Type} {encode : α → CIL.Value}
    {operation : BitVec 256 → α → CIL.Value} {first : Bool}
    {program : CIL.Program} {p q : CIL.FeatureProfile} {method : Nat}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (proof : OrderedScalarContract first encode operation program method) :
    OrderedScalarContract first encode operation (CIL.reprofile program q) method := by
  intro memory input scalar call
  obtain ⟨fuel, final, certificate, preserved⟩ := proof memory input scalar
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, preserved⟩

#print axioms OrderedScalarContract.reprofile
end UInt256Model.Safety
