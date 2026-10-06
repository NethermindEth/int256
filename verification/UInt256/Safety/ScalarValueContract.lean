import UInt256.Safety.ProfileContracts

namespace UInt256Model.Safety
open CIL.Safety

def scalarValueArguments (word : CIL.Value) (input : BitVec 256) : List Value :=
  [.scalar word, .scalar (.v256 input)]

/-- Both operands are passed values. Address-taking inside the callee must use
    initialized private storage; every pre-existing caller byte is preserved. -/
def ScalarValueContract {α : Type} (encode : α → CIL.Value)
    (operation : α → BitVec 256 → CIL.Value) (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (word : α) (input : BitVec 256),
    CallingConditions program memory [] [] →
    ∃ fuel final,
      InvocationCertificate program method (scalarValueArguments (encode word) input) memory fuel final
        [.scalar (operation word input)] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

theorem ScalarValueContract.reprofile {α : Type} {encode : α → CIL.Value}
    {operation : α → BitVec 256 → CIL.Value} {program : CIL.Program} {method : Nat}
    {p q : CIL.FeatureProfile} (uniform : ∀ body ∈ program, body.profile = p)
    (agreement : program.ProfileAgreement p q)
    (proof : ScalarValueContract encode operation program method) :
    ScalarValueContract encode operation (CIL.reprofile program q) method := by
  intro memory word input call
  obtain ⟨fuel, final, certificate, preserved⟩ := proof memory word input
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, preserved⟩

#print axioms ScalarValueContract.reprofile
end UInt256Model.Safety
