import UInt256.Safety.InitializedOutput
import UInt256.Safety.ProfileContracts

namespace UInt256Model.Safety
open CIL.Safety

def unaryArguments (input output : Reference) : List Value :=
  [.reference (.address input), .reference (.address output)]

/-- A complete initialized output snapshot, usable by a caller that reads the result. -/
def InitializedUnaryContract (operation : BitVec 256 → BitVec 256)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (input output : Reference),
    CallingConditions program memory [input] [output] →
    ∃ fuel final,
      InvocationCertificate program method (unaryArguments input output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (operation (inputValue memory input)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

theorem InitializedUnaryContract.reprofile {program : CIL.Program} {p q : CIL.FeatureProfile}
    {method : Nat} {operation : BitVec 256 → BitVec 256}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (proof : InitializedUnaryContract operation program method) :
    InitializedUnaryContract operation (CIL.reprofile program q) method := by
  intro memory input output call
  obtain ⟨fuel, final, certificate, postcondition⟩ := proof memory input output
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, postcondition⟩

#print axioms InitializedUnaryContract.reprofile
end UInt256Model.Safety
