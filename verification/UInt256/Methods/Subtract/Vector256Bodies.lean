import UInt256.Generated.MethodTemplates
import CIL.Instructions

namespace UInt256Proof.Subtract.Vector256

/-- `SubtractImpl` under AVX2; the flags select the AVX512VL borrow masks and the BMI1 flag extraction. -/
def subtractImplBody (profile : CIL.FeatureProfile) (avx512 bmi1 : Bool) (lookup : Nat) :
    CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize (← `(
    let template := UInt256Proof.Generated.Method.method5 $(Lean.mkIdent `profile)
      true $(Lean.mkIdent `avx512) true $(Lean.mkIdent `lookup)
    let unavailable : CIL.Op := .unsupported "Unreachable under selected profile"
    let scalarFlag : List CIL.Op := [.local 6, .const32 (BitVec.ofInt 32 16), .band,
      .const32 0, .gtu, .ret (some .unsigned8)]
    { template with code := template.code.take 104 ++
      scalarFlag.map (fun op => if $(Lean.mkIdent `bmi1) then unavailable else op) ++
      (template.code.drop 110 |>.take 7).map (fun op =>
        if $(Lean.mkIdent `bmi1) then op else unavailable) ++
      template.code.drop 117 })) none
  let names := #[``UInt256Proof.Generated.Method.method5, ``List.take,
    ``List.drop, ``List.map, ``List.append, ``HAppend.hAppend, ``Append.append]
  let rules ← names.foldlM (fun rules name => rules.addDeclToUnfold name)
    ({} : Lean.Meta.SimpTheorems)
  let context ← Lean.Meta.Simp.mkContext (simpTheorems := #[rules])
  let normalized := (← Lean.Meta.dsimp body context).1
  let rules ← #[``eq_self, ``ite_true, ``ite_false].foldlM
    (fun rules name => rules.addConst name) ({} : Lean.Meta.SimpTheorems)
  let context ← Lean.Meta.Simp.mkContext (simpTheorems := #[rules])
  return (← Lean.Meta.simp normalized context).1.expr

def subtractEntryBody (profile : CIL.FeatureProfile) (impl : Nat) : CIL.Method := { profile := profile, returnsValue := false, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .arg 1,
  .arg 2,
  .call impl 3,
  .pop,
  .ret] }
def subtractUnderflowEntryBody (profile : CIL.FeatureProfile) (impl : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .arg 1,
  .arg 2,
  .call impl 3,
  .ret (some .unsigned8)] }

end UInt256Proof.Subtract.Vector256
