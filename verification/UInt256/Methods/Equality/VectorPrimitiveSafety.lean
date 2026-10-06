import Extracted
import UInt256.Safety.ReadOnlyScalarExecution
import UInt256.Methods.Equality.VectorLemmas
import UInt256.Methods.Bitwise.Lemmas
import CIL.Safety.StepComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def vectorPrimitiveIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.vector (.equalsAll 256)) _ => true | _ => false

def vectorPrimitiveBody : CIL.Method := Extracted.program[vectorPrimitiveIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem vector_primitive_found : Extracted.program[vectorPrimitiveIndex]? = some vectorPrimitiveBody := by rfl

theorem vector_primitive_fits (left : Reference) (argument : CIL.Value) :
    FrameSetupFits vectorPrimitiveBody (scalarArguments left argument) := by
  conv in vectorPrimitiveBody => cbv
  simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit]

#print axioms vector_primitive_found
#print axioms vector_primitive_fits

end UInt256Proof.Equality.Safety
