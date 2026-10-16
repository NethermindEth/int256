import UInt256.Safety.Calling
import UInt256.Safety.OutputAccess
import UInt256.Methods.Shift.Contract
import CIL.Safety.Certificate
import UInt256.Safety.ProfileContracts

namespace UInt256Model.Safety
open CIL.Safety

def shiftArguments (input : Reference) (count : BitVec 32) (output : Reference) : List Value :=
  [.reference (.address input), .scalar (.i32 count), .reference (.address output)]

/-- The full signed-count result, checked execution, initialized output and caller
    footprint refer to the same invocation and initial operand bytes. -/
def ShiftInvocation (direction : UInt256Proof.Shift.Direction) (program : CIL.Program) (entry : Nat)
    (memory : Memory) (input : Reference) (count : BitVec 32) (output : Reference) : Prop :=
    ∃ fuel final,
      InvocationCertificate program entry (shiftArguments input count output) memory fuel final [] ∧
      inputValue final output = UInt256Proof.Shift.result direction (inputValue memory input) count ∧
      access final output 32 1 true = .ok () ∧
      (∃ bytes, read final output 32 1 = .ok bytes) ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

def ShiftContract (direction : UInt256Proof.Shift.Direction) (program : CIL.Program) (entry : Nat) : Prop :=
  ∀ (memory : Memory) (input : Reference) (count : BitVec 32) (output : Reference),
    CallingConditions program memory [input] [output] →
    ShiftInvocation direction program entry memory input count output


theorem ShiftContract.reprofile {direction : UInt256Proof.Shift.Direction}
    {program : CIL.Program} {entry : Nat} {p q : CIL.FeatureProfile}
    (uniform : ∀ body ∈ program, body.profile = p) (agreement : program.ProfileAgreement p q)
    (proof : ShiftContract direction program entry) :
    ShiftContract direction (CIL.reprofile program q) entry := by
  intro memory input count output call
  obtain ⟨fuel, final, certificate, postcondition⟩ := proof memory input count output
    ((callingConditions_reprofile _ _ _ _ _).mp call)
  exact ⟨fuel, final, invocationCertificate_uniform_reprofile _ _ _ uniform agreement
    _ _ _ _ _ _ certificate, postcondition⟩

#print axioms ShiftContract.reprofile

end UInt256Model.Safety
