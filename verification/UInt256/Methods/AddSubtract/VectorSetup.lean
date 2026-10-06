import Extracted
import CIL.Safety.NumericHomes

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety

/-- Discover operand-loading lane arithmetic, excluding the later lookup-based
    carry repair helper. Execution proofs still check the selected body. -/
def vectorIndex : Nat := Extracted.program.findIdx fun body =>
  (body.code.any fun op => match op with | .memory .bitcast256 => true | _ => false) &&
  body.code.any fun op =>
    match op with
    | .intrinsic (.vector (.add64 256)) _ | .intrinsic (.vector (.sub64 256)) _ => true
    | _ => false

def vectorBody : CIL.Method := Extracted.program[vectorIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def vectorSpecs : List NumericLocalSpec := numericSpecs vectorBody

theorem vector_local_metadata :
    vectorBody.localKinds = vectorSpecs.map NumericLocalSpec.kind ∧
    vectorBody.locals = vectorSpecs.map NumericLocalSpec.value := by
  constructor <;> rfl

theorem vector_frame_setup (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame vectorBody args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity vectorSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup vectorBody vectorSpecs vector_local_metadata.1 vector_local_metadata.2
    (by rfl) memory args wf

#print axioms vector_local_metadata
#print axioms vector_frame_setup
end UInt256Proof.AddSubtract.Safety
