import UInt256.Methods.Multiply.HomeStorage
open Lean Meta Elab Tactic CIL UInt256Model UInt256Proof
namespace UInt256Proof.Multiply
elab "cil_home_multiply_store_call" : tactic => withMainContext do
  for expression in collectRuns (← getMainTarget) do
    if expression.hasLooseBVars then continue
    let call := expression.getAppArgs
    unless ← isDefEq call[3]! (mkNatLit 0) do continue
    let .lit (.natVal index) ← whnf call[2]! | continue
    let summary := `UInt256Proof.Multiply |>.str s!"execute_home_storage_{index}"
    unless (← getEnv).contains summary do continue
    let values ← listTerms call[4]!
    unless values.size == 5 do continue
    let reference ← whnf (← constructorArg ``CIL.Value.ref values[0]!)
    unless reference.isAppOfArity ``CIL.Address.home 4 do continue
    let fields := reference.getAppArgs
    unless ← isDefEq fields[3]! (mkNatLit 0) do continue
    let outFrame ← PrettyPrinter.delab fields[0]!
    let outKind ← PrettyPrinter.delab fields[1]!
    let outIndex ← PrettyPrinter.delab fields[2]!
    let mut words : Array Term := #[]
    for value in values[1:] do
      words := words.push (← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 value))
    let contract := mkIdent summary
    let memory ← PrettyPrinter.delab call[7]!
    let frame ← PrettyPrinter.delab call[5]!
    let fuel ← PrettyPrinter.delab call[1]!
    let final := mkIdent (← mkFreshUserName `productMemory)
    let run := mkIdent (← mkFreshUserName `productStoreRun)
    let output := mkIdent (← mkFreshUserName `productHomeOutput)
    let bytes := mkIdent (← mkFreshUserName `productStoreBytes)
    let locals := mkIdent (← mkFreshUserName `productStoreLocals)
    let r0 := words[0]!
    let r1 := words[1]!
    let r2 := words[2]!
    let r3 := words[3]!
    evalTactic (← `(tactic|
      obtain ⟨$final:ident, $run:ident, $output:ident, $bytes:ident, $locals:ident⟩ :=
        $contract $memory $frame $fuel $outFrame $outKind $outIndex $r0 $r1 $r2 $r3
          (by simp [cil_code]; all_goals omega)))
    rewriteHelperRun run
    return
  throwError "No proved multiplication storage call"
end UInt256Proof.Multiply

