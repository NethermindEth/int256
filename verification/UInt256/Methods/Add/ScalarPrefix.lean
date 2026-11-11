import UInt256.Methods.Add.Bindings
import CIL.Safety.StepComposition
import CIL.Safety.WordLocals
import CIL.Safety.MethodContract

namespace UInt256Proof.Safety

open CIL.Safety

/-- Discover the first reachable small-operand decision from extracted CIL. -/
def scalarFirstDecision : Nat :=
  Extracted.addScalarBody.code.findIdx fun op => match op with
    | .brnonzero _ => true
    | _ => false

/-- The second small-operand decision is discovered after the first one. -/
def scalarSecondDecision : Nat :=
  scalarFirstDecision + 1 +
    (Extracted.addScalarBody.code.drop (scalarFirstDecision + 1)).findIdx (fun op =>
      match op with | .brnonzero _ => true | _ => false)

end UInt256Proof.Safety
