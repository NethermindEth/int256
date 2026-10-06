import UInt256.Methods.Add.VectorParentCall

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Discover the lookup-based correction helper, distinct from preparation. -/
def repairIndex : Nat := Extracted.program.findIdx fun body =>
  (body.code.any fun op => match op with | .memory .spanReference => true | _ => false) &&
  body.code.any fun op => match op with
    | .intrinsic (.vector (.add64 256)) _ => true
    | _ => false

def repairBody : CIL.Method := Extracted.program[repairIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def repairSpecs : List NumericLocalSpec := numericSpecs repairBody

def repairArguments (sum generated propagation : BitVec 256) (output : Reference) : List Value :=
  [.scalar (.v256 sum), .scalar (.v256 generated), .scalar (.v256 propagation),
    .reference (.address output)]

theorem repair_frame_setup (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame repairBody args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity repairSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup repairBody repairSpecs (by rfl) (by rfl)
    (by rfl) memory args wf

#print axioms repair_frame_setup
end UInt256Proof.Add.Safety
