import CIL.Safety.ProfileCertificate
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.ReadOnlyScalarContract
import UInt256.Safety.ReadOnlyValueContract
import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.Contract

namespace UInt256Model.Safety
open CIL.Safety

@[simp] theorem callingConditions_reprofile (program : CIL.Program) (profile : CIL.FeatureProfile)
    (memory : Memory) (inputs outputs : List Reference) :
    CallingConditions (CIL.reprofile program profile) memory inputs outputs ↔
      CallingConditions program memory inputs outputs := by
  simp only [CallingConditions, programStaticDescriptors_reprofile]

variable {program : CIL.Program} {p q : CIL.FeatureProfile} {method : Nat}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)

include uniform agreement

theorem ReadOnlyContract.reprofile {operation : List (BitVec 256) → CIL.Value} {arity : Nat}
    (proof : ReadOnlyContract operation program method arity) :
    ReadOnlyContract operation (CIL.reprofile program q) method arity := by
  intro memory inputs length call
  obtain ⟨fuel, final, certificate, preserved⟩ := proof memory inputs length
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, preserved⟩

theorem ReadOnlyScalarContract.reprofile {α : Type} {encode : α → CIL.Value}
    {operation : BitVec 256 → α → CIL.Value}
    (proof : ReadOnlyScalarContract encode operation program method) :
    ReadOnlyScalarContract encode operation (CIL.reprofile program q) method := by
  intro memory left right call
  obtain ⟨fuel, final, certificate, preserved⟩ := proof memory left right
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, preserved⟩

theorem ReadOnlyValueContract.reprofile {operation : BitVec 256 → BitVec 256 → CIL.Value}
    (proof : ReadOnlyValueContract operation program method) :
    ReadOnlyValueContract operation (CIL.reprofile program q) method := by
  intro memory left right call
  obtain ⟨fuel, final, certificate, preserved⟩ := proof memory left right
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, preserved⟩

theorem ScalarOperatorContract.reprofile {α : Type} {encode : α → CIL.Value}
    {equal : BitVec 256 → α → Bool} {first negate : Bool}
    (proof : ScalarOperatorContract first negate encode equal program method) :
    ScalarOperatorContract first negate encode equal (CIL.reprofile program q) method := by
  intro memory left right call
  obtain ⟨fuel, final, certificate, preserved⟩ := proof memory left right
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, preserved⟩

theorem WrappingBinaryContract.reprofile {operation : BitVec 256 → BitVec 256 → BitVec 256}
    (proof : WrappingBinaryContract operation program method) :
    WrappingBinaryContract operation (CIL.reprofile program q) method := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, postcondition⟩ := proof memory left right output
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, postcondition⟩

#print axioms callingConditions_reprofile
#print axioms ReadOnlyContract.reprofile
#print axioms ReadOnlyScalarContract.reprofile
#print axioms ReadOnlyValueContract.reprofile
#print axioms ScalarOperatorContract.reprofile
#print axioms WrappingBinaryContract.reprofile
end UInt256Model.Safety
