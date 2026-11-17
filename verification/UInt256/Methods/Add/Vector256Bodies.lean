import UInt256.Generated.MethodTemplates
import CIL.Instructions

namespace UInt256Proof.Add.Vector256

/-- `PrepareAdd` under AVX2; the flag selects the AVX512VL carry masks. -/
def prepareAddBody (profile : CIL.FeatureProfile) (avx512 : Bool) : CIL.Method :=
  UInt256Proof.Generated.Method.method21 profile avx512

def finishAddBody (profile : CIL.FeatureProfile) (lookup : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method4 $(Lean.mkIdent `profile) $(Lean.mkIdent `lookup))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)
def addEntryBody (profile : CIL.FeatureProfile) (finish prepare : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method12 $(Lean.mkIdent `profile) true $(Lean.mkIdent `finish) $(Lean.mkIdent `prepare))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)
def addOverflowEntryBody (profile : CIL.FeatureProfile) (finish prepare : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method0 $(Lean.mkIdent `profile) true $(Lean.mkIdent `finish) $(Lean.mkIdent `prepare))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

end UInt256Proof.Add.Vector256
