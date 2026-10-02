import UInt256.StorageContracts

open Lean Meta Elab Tactic
open CIL UInt256Model
namespace UInt256Proof

partial def listTerms (expression : Expr) : MetaM (Array Expr) := do
  let expression ← whnf expression
  if expression.isAppOf ``List.nil then return #[]
  let args := expression.getAppArgs
  unless expression.isAppOf ``List.cons && args.size == 3 do
    throwError "Expected a concrete execution argument list"
  return #[args[1]!] ++ (← listTerms args[2]!)

def constructorArg (name : Name) (expression : Expr) : MetaM Expr := do
  let expression ← whnf expression
  unless expression.isAppOfArity name 1 do
    throwError "Unsupported argument for proved helper contract: {expression}"
  return expression.getAppArgs[0]!

partial def collectRuns (expression : Expr) : Array Expr := Id.run do
  let mut result := #[]
  if expression.isAppOfArity ``CIL.run 8 then result := result.push expression
  match expression with
  | .app fn arg => return result ++ collectRuns fn ++ collectRuns arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
    return result ++ collectRuns domain ++ collectRuns body
  | .letE _ type value body _ =>
    return result ++ collectRuns type ++ collectRuns value ++ collectRuns body
  | .mdata _ body | .proj _ _ body => return result ++ collectRuns body
  | _ => return result

-- A signature candidate is usable only after its current body has been proved.
def provedCall (index summary : Name) (label : String) (arity : Nat) :
    TacticM (Array Expr × Array Expr) := do
  unless (← getEnv).contains index && (← getEnv).contains summary do
    throwError "No proved summary available"
  for candidate in collectRuns (← getMainTarget) do
    if candidate.hasLooseBVars then continue
    let call := candidate.getAppArgs
    if (← isDefEq call[2]! (mkConst index)) && (← isDefEq call[3]! (mkNatLit 0)) then
      let values ← listTerms call[4]!
      unless values.size == arity do throwError "{label} helper argument count changed"
      return (call, values)
  throwError "No applicable proved {label} helper call"

def rewriteHelperRun (hr : Ident) : TacticM Unit := do
  evalTactic (← `(tactic| simp [cil_code, initLocals] at $hr:ident))
  evalTactic (← `(tactic| rw [$hr:ident]))
  evalTactic (← `(tactic| simp only [Option.bind_some]))

elab "cil_store_call" : tactic => withMainContext do
  let (call, values) ← provedCall `Extracted.storeLimbsIndex
    `UInt256Proof.execute_store_contract "storage" 5
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let mut words : Array Term := #[]
  for value in values[1:] do
    words := words.push (← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 value))
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `storedMemory)
  let hr := mkIdent (← mkFreshUserName `storeRun)
  let hb := mkIdent (← mkFreshUserName `storeBytes)
  let hl := mkIdent (← mkFreshUserName `storeLocals)
  let r0 := words[0]!
  let r1 := words[1]!
  let r2 := words[2]!
  let r3 := words[3]!
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $hr:ident, $hb:ident, $hl:ident⟩ :=
      execute_store_contract $memory $frame $fuel $out $r0 $r1 $r2 $r3
        (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun hr

def wordHelperCall (index summary : Name) (label : String) (bound : Ident)
    (reads : TSyntax `tactic) : TacticM Unit := do
  let contract := mkIdent summary
  let (call, values) ← provedCall index summary label 4
  let x ← constructorArg ``CIL.Value.i64 values[0]!
  let y ← constructorArg ``CIL.Value.i64 values[1]!
  let ca ← constructorArg ``CIL.Value.ref values[2]!
  let ra ← constructorArg ``CIL.Value.ref values[3]!
  unless ca.isAppOfArity ``CIL.Address.local 2 && ra.isAppOfArity ``CIL.Address.local 2 do
    throwError "Word contract requires caller-local references"
  let caArgs := ca.getAppArgs
  let raArgs := ra.getAppArgs
  unless ← isDefEq caArgs[0]! raArgs[0]! do
    throwError "Word references occupy different caller frames"
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab caArgs[0]!
  let fuel ← PrettyPrinter.delab call[1]!
  let cslot ← PrettyPrinter.delab caArgs[1]!
  let rslot ← PrettyPrinter.delab raArgs[1]!
  let xTerm ← PrettyPrinter.delab x
  let yTerm ← PrettyPrinter.delab y
  let final := mkIdent (← mkFreshUserName `calleeMemory)
  let hr := mkIdent (← mkFreshUserName `calleeRun)
  let hc := mkIdent (← mkFreshUserName `calleeCarry)
  let hs := mkIdent (← mkFreshUserName `calleeSum)
  let hp := mkIdent (← mkFreshUserName `calleePreserved)
  let hb := mkIdent (← mkFreshUserName `calleeBytes)
  let hl := mkIdent (← mkFreshUserName `calleeLocals)
  let hread := mkIdent (← mkFreshUserName `calleeReads)
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $hr:ident, $hc:ident, $hs:ident, $hp:ident⟩ :=
      $contract:ident $memory $frame $fuel $cslot $rslot $xTerm $yTerm _
        (by $reads:tactic)
        (by omega)
        (by repeat first | apply $bound:ident | assumption | decide)
        (by simp [cil_code]; all_goals omega)))
  evalTactic (← `(tactic|
    have $hb:ident : ∀ address, $final (.byte address) = $memory (.byte address) := by
      intro address
      apply $hp
      all_goals simp))
  evalTactic (← `(tactic|
    have $hl:ident : ∀ index, index ≠ $cslot → index ≠ $rslot →
        $final (.local $frame index) = $memory (.local $frame index) := by
      intro index hcarry hsum
      apply $hp
      · intro other index hlower; intro h; have := Address.local.inj h; omega
      · simpa using hcarry
      · simpa using hsum))
  evalTactic (← `(tactic|
    have $hread:ident : ∀ base, read64 $final (.byte base) = read64 $memory (.byte base) := by
      intro base
      exact read64_congr $final $memory $hb base))
  rewriteHelperRun hr

def smallHelperCall (index summary : Name) (label : String) : TacticM Unit := do
  let contract := mkIdent summary
  let (call, values) ← provedCall index summary label 3
  let base ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let word ← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 values[1]!)
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[2]!)
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `smallMemory)
  let flag := mkIdent (← mkFreshUserName `smallFlag)
  let hr := mkIdent (← mkFreshUserName `smallRun)
  let hb := mkIdent (← mkFreshUserName `smallBytes)
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $flag:ident, $hr:ident, $hb:ident⟩ :=
      $contract:ident $memory $base $out $frame $fuel _ $word
        (by intro i; simp_all [initLocals]; all_goals rfl)
        (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun hr

-- Use memory congruence only when the extracted and specified stored words
-- already agree. Comparing whole memory functions can hide a wrong arithmetic
-- result behind expensive definitional unfolding of every byte write.
elab "cil_preserved_store" : tactic => withMainContext do
  let target ← getMainTarget
  let some (_, left, right) := target.eq? | throwError "Expected a storage equality"
  unless left.getAppFn.isConstOf ``UInt256Proof.store4 &&
      right.getAppFn.isConstOf ``UInt256Proof.store4 do
    throwError "Extracted storage does not match the required postcondition:\n⊢ {target}"
  let actual := left.getAppArgs
  let expected := right.getAppArgs
  unless actual.size == 7 && expected.size == 7 do
    throwError "Expected a fully applied four-word storage equation"
  for index in [1:7] do
    unless ← isDefEq actual[index]! expected[index]! do
      throwError "Extracted storage operands differ from the required result:\n⊢ {target}"
  let address ← PrettyPrinter.delab (← constructorArg ``CIL.Address.byte actual[6]!)
  evalTactic (← `(tactic| apply store4_bytes _ _ ?_ _ _ _ _ _ $address))

-- Split only a conditional instruction address, never a comparison flag that
-- can instead be folded into a mathematical carry.
elab "cil_branch" : tactic => withMainContext do
  for candidate in collectRuns (← getMainTarget) do
    if candidate.hasLooseBVars then continue
    let pc := candidate.getAppArgs[3]!
    if pc.isAppOfArity ``ite 5 then
      let condition ← PrettyPrinter.delab pc.getAppArgs[1]!
      let h := mkIdent (← mkFreshUserName `branchCondition)
      let hTerm : Term := ⟨h.raw⟩
      evalTactic (← `(tactic| by_cases $h:ident : $condition <;> simp only [$hTerm:term, ↓reduceIte]))
      return
  throwError "No conditional instruction address"

macro "cil_execute_core" facts:term,+ "with" calls:tacticSeq : tactic =>
  `(tactic| ((try (simp only [cil_code])); repeat'
    first
    | ($calls:tacticSeq)
    | cil_branch
    | (rw [CIL.run]
       -- Fetch first, then retain rewrite proofs for the selected instruction.
       -- This avoids both speculative simplification and repeated kernel reduction.
       simp only [List.getElem_eq_getElem?_get, cil_code, Option.get_some,
         Option.pure_def, Option.bind_eq_bind, Option.bind_some]
       simp (config := { implicitDefEqProofs := false })
         [*, cil_code, CIL.step, CIL.binary, CIL.truth, CIL.initLocals, CIL.write64,
         CIL.FeatureProfile.evaluate, CIL.Intrinsic.available,
         read64_local, write_local_read_local, fin_val_three, $[$facts:term],*]
)))


end UInt256Proof
