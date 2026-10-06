import UInt256.Safety.ProfileContracts

namespace UInt256Model.Safety
open CIL.Safety

/-- The returned flag and stored result are independent functions of the initial
    operands. The checked invocation retains valid overlap and caller storage. -/
def ReportingBinaryContract (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (flag : BitVec 256 → BitVec 256 → Bool) (program : CIL.Program) (method : Nat) : Prop :=
  ∀ (memory : Memory) (left right output : Reference),
    CallingConditions program memory [left, right] [output] →
    ∃ fuel final,
      InvocationCertificate program method (binaryArguments left right output) memory fuel final
        [.scalar (.i32 (if flag (inputValue memory left) (inputValue memory right) then 1 else 0))] ∧
      inputValue final output = operation (inputValue memory left) (inputValue memory right) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

theorem ReportingBinaryContract.reprofile
    {operation : BitVec 256 → BitVec 256 → BitVec 256} {flag : BitVec 256 → BitVec 256 → Bool}
    {program : CIL.Program} {method : Nat} {p q : CIL.FeatureProfile}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (proof : ReportingBinaryContract operation flag program method) :
    ReportingBinaryContract operation flag (CIL.reprofile program q) method := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, preserved⟩ := proof memory left right output
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, preserved⟩

#print axioms ReportingBinaryContract.reprofile
end UInt256Model.Safety
