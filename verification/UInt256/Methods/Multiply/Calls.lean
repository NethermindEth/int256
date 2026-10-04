import UInt256.Methods.Multiply.StorageEquality
import UInt256.Methods.Multiply.Storage
import UInt256.Methods.Multiply.WideExecution
import UInt256.Methods.Multiply.CountExecution
import UInt256.Methods.Multiply.VectorProducts
import UInt256.Methods.Multiply.CountPermutation
open Lean Meta Elab Tactic CIL UInt256Model UInt256Proof
namespace UInt256Proof.Multiply

def productWordCall (index summary : Name) (counted : Bool) : TacticM Unit := do
  let (call, values) ← provedCall index summary "multiplication word" 3
  let a ← Term.exprToSyntax (← constructorArg ``CIL.Value.i64 values[0]!)
  let b ← Term.exprToSyntax (← constructorArg ``CIL.Value.i64 values[1]!)
  let reference ← whnf (← constructorArg ``CIL.Value.ref values[2]!)
  unless reference.isAppOfArity ``CIL.Address.local 2 do
    throwError "Word-product output must occupy a caller-local word"
  let fields := reference.getAppArgs
  let outputFrame ← Term.exprToSyntax fields[0]!
  let outputIndex ← Term.exprToSyntax fields[1]!
  let memory ← Term.exprToSyntax call[7]!
  let frame ← Term.exprToSyntax call[5]!
  let fuel ← Term.exprToSyntax call[1]!
  let contract := mkIdent summary
  let final := mkIdent (← mkFreshUserName `wordProductMemory)
  let run := mkIdent (← mkFreshUserName `wordProductRun)
  let locals := mkIdent (← mkFreshUserName `wordProductLocals)
  let bytes := mkIdent (← mkFreshUserName `wordProductBytes)
  let parentLocals := mkIdent (← mkFreshUserName `wordProductParentLocals)
  let outputWord := mkIdent (← mkFreshUserName `wordProductOutput)
  let separate := mkIdent (← mkFreshUserName `wordProductSeparate)
  evalTactic (← `(tactic| have $separate:ident : $outputFrame ≠ $frame := by omega))
  if counted then
    let context ← mkSimpContext (← `(tactic| simp [*, initLocals, write_local_read_local])) false
    let query := mkApp call[7]! reference
    let (simplified, _) ← Meta.simp query context.ctx context.simprocs
    let value ← whnf simplified.expr
    unless value.isAppOfArity ``Option.some 2 do
      throwError "The caller carry word is not initialized"
    let count ← Term.exprToSyntax (← constructorArg ``CIL.Value.i64 value.getAppArgs[1]!)
    evalTactic (← `(tactic|
      obtain ⟨$final:ident, $run:ident, $locals:ident, $bytes:ident⟩ :=
        $contract $memory $frame $fuel $outputFrame $outputIndex $a $b $count
          (by omega) (by simp [*, initLocals, write_local_read_local]; all_goals rfl)
          (by simp [cil_code]; all_goals omega)))
  else
    evalTactic (← `(tactic|
      obtain ⟨$final:ident, $run:ident, $locals:ident, $bytes:ident⟩ :=
        $contract $memory $frame $fuel $outputFrame $outputIndex $a $b
          (by omega) (by simp [cil_code]; all_goals omega)))
  Term.synthesizeSyntheticMVarsNoPostponing
  evalTactic (← `(tactic|
    have $parentLocals:ident : ∀ slot, slot ≠ $outputIndex →
        $final (.local $outputFrame slot) = $memory (.local $outputFrame slot) := by
      intro slot different
      rw [$locals _ _ (by omega)]
      simp [write, different, $separate:ident, Ne.symm $separate:ident]))
  evalTactic (← `(tactic| have $outputWord:ident := $locals $outputFrame $outputIndex (by omega)))
  evalTactic (← `(tactic| try simp only [write, ↓reduceIte] at $outputWord:ident))
  let reads := mkIdent (← mkFreshUserName `wordProductReads)
  evalTactic (← `(tactic|
    have $reads:ident : ∀ base, read64 $final (.byte base) = read64 $memory (.byte base) := by
      intro base
      exact read64_congr $final $memory $bytes base))
  rewriteHelperRun run

elab "cil_wide_product_call" : tactic => withMainContext do
  for expression in collectRuns (← getMainTarget) do
    if expression.hasLooseBVars then continue
    let call := expression.getAppArgs
    unless ← isDefEq call[3]! (mkNatLit 0) do continue
    let .lit (.natVal index) ← whnf call[2]! | continue
    let summary := `UInt256Proof.Multiply |>.str s!"execute_wide_product_{index}"
    let indexName := `UInt256Proof.Multiply |>.str s!"wide_product_index_{index}"
    unless (← getEnv).contains summary && (← getEnv).contains indexName do continue
    let saved ← saveState
    try
      productWordCall indexName summary false
      return
    catch _ => saved.restore
  throwError "No applicable proved wide-product call"

elab "cil_count_carry_call" : tactic => withMainContext do
  productWordCall `Extracted.carryCountIndex `UInt256Proof.Multiply.execute_count_carry true

elab "multiply_checked_case " theoremName:ident " (" arguments:term,* ")" : tactic => withMainContext do
  let some (.thmInfo _) := (← getEnv).find? theoremName.getId |
    throwError "No checked public-case summary is available"
  let saved ← saveState
  try
    let mut applied : Term := theoremName
    for argument in arguments.getElems do
      applied ← `(term| $applied $argument)
    evalTactic (← `(tactic| exact $applied))
  catch error =>
    saved.restore
    throw error


elab "multiply_storage_congruence" : tactic => withMainContext do
  let target ← getMainTarget
  let some (_, left, right) := target.eq? | throwError "Expected a storage equality"
  unless left.getAppFn.isConstOf ``UInt256Proof.store4 &&
      right.getAppFn.isConstOf ``UInt256Proof.store4 do
    throwError "Expected two stored four-word outputs"
  let actual := left.getAppArgs
  let expected := right.getAppArgs
  unless actual.size == 7 && expected.size == 7 do
    throwError "Expected fully applied four-word outputs"
  unless (← isDefEq actual[1]! expected[1]!) && (← isDefEq actual[6]! expected[6]!) do
    throwError "Stored output addresses differ"
  let mut applied : Term := mkIdent ``store4_bytes_of_word_eq
  for argument in #[actual[0]!, expected[0]!, actual[1]!,
      actual[2]!, actual[3]!, actual[4]!, actual[5]!,
      expected[2]!, expected[3]!, expected[4]!, expected[5]!] do
    let term ← Term.exprToSyntax argument
    applied ← `(term| $applied $term)
  let address ← Term.exprToSyntax (← constructorArg ``CIL.Address.byte actual[6]!)
  evalTactic (← `(tactic| apply $applied ?_ ?_ ?_ ?_ ?_ $address))

elab "multiply_without_recovery " body:tacticSeq : tactic =>
  Term.withoutErrToSorry <| Tactic.withoutRecover <| evalTactic body

end UInt256Proof.Multiply

