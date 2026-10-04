import UInt256.Methods.Multiply.HomeCalls
import UInt256.Methods.Multiply.HomeWordAll
open Lean Meta Elab Tactic CIL UInt256Model UInt256Proof
namespace UInt256Proof.Multiply
elab "cil_home_scalar_product_call " a:term "," b:term "," leftReads:term "," rightReads:term : tactic => withMainContext do
  for expression in collectRuns (← getMainTarget) do
    if expression.hasLooseBVars then continue
    let call := expression.getAppArgs
    unless ← isDefEq call[3]! (mkNatLit 0) do continue
    let .lit (.natVal index) ← whnf call[2]! | continue
    let summary := `UInt256Proof.Multiply |>.str s!"execute_home_word_all_{index}"
    unless (← getEnv).contains summary do continue
    let values ← listTerms call[4]!
    unless values.size == 3 do continue
    let input ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
    let word ← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 values[1]!)
    let reference ← whnf (← constructorArg ``CIL.Value.ref values[2]!)
    unless reference.isAppOfArity ``CIL.Address.home 4 do continue
    let fields := reference.getAppArgs
    unless ← isDefEq fields[3]! (mkNatLit 0) do continue
    let outFrame ← PrettyPrinter.delab fields[0]!
    let outKind ← PrettyPrinter.delab fields[1]!
    let outIndex ← PrettyPrinter.delab fields[2]!
    let memory ← PrettyPrinter.delab call[7]!
    let frame ← PrettyPrinter.delab call[5]!
    let fuel ← PrettyPrinter.delab call[1]!
    let number := Syntax.mkNumLit (toString index)
    for (limbs, fact) in [(a,leftReads),(b,rightReads)] do
      let saved ← saveState
      try
        let contract := mkIdent summary
        let final := mkIdent (← mkFreshUserName `scalarProductMemory)
        let run := mkIdent (← mkFreshUserName `scalarProductRun)
        let output := mkIdent (← mkFreshUserName `scalarProductOutput)
        let bytes := mkIdent (← mkFreshUserName `scalarProductBytes)
        let adjustment := mkIdent (← mkFreshUserName `scalarProductFuel)
        let proved := mkIdent (← mkFreshUserName `scalarProductProof)
        evalTactic (← `(tactic|
          have $proved:ident :=
            $contract $memory $input $frame
              ($fuel - executionBound Extracted.program $number) $outFrame $outKind $outIndex $limbs $word
              (by
                intro i
                try simp only [read64_write_local_byte, read64_initLocals_byte]
                exact $fact i)))
        evalTactic (← `(tactic|
          obtain ⟨$final:ident, $run:ident, $output:ident, $bytes:ident⟩ := $proved:term))
        evalTactic (← `(tactic|
          have $adjustment:ident : $fuel - executionBound Extracted.program $number +
              executionBound Extracted.program $number = $fuel := by
            apply Nat.sub_add_cancel
            try simp [cil_code]
            all_goals omega))
        evalTactic (← `(tactic| rw [$adjustment:term] at $run:ident))
        rewriteHelperRun run
        return
      catch _ => saved.restore
  throwError "No applicable proved scalar-product call"
end UInt256Proof.Multiply

