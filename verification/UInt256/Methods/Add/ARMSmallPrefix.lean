import UInt256.Generated.AddTemplates
import UInt256.Methods.Add.ARMBody
import CIL.Safety.ReturnArity
import UInt256.Methods.Reporting.Arithmetic
import CIL.Safety.ReturnMemory
import UInt256.Methods.Multiply.LimbStorage
import CIL.Safety.CallComposition
import UInt256.Safety.NumericStore
import CIL.Safety.StepComposition
import CIL.Safety.MethodContract
import CIL.Safety.WordLocals
import CIL.Safety.NumericHomes

/-! The extracted ARM small-add body and its argument encoding. -/

namespace UInt256Proof.Add.Safety

open CIL.Safety

def armSmallBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Add.method1
      $(Lean.mkIdent `profile) true $(Lean.mkIdent `storage))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

def armSmallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

end UInt256Proof.Add.Safety
