import UInt256.Methods.Multiply.LimbExecution
import UInt256.Methods.Multiply.LimbLeftTwoExecution
import UInt256.Methods.Multiply.LimbBothTwoExecution
open Lean Meta Elab Tactic CIL UInt256Model UInt256Proof
namespace UInt256Proof.Multiply
elab "cil_limb_product_call " a:term "," b:term "," leftReads:term "," rightReads:term : tactic => withMainContext do
  for expression in collectRuns (← getMainTarget) do
    if expression.hasLooseBVars then continue
    let call := expression.getAppArgs
    unless ← isDefEq call[3]! (mkNatLit 0) do continue
    let .lit (.natVal index) ← whnf call[2]! | continue
    let environment ← getEnv
    unless ["", "LeftTwo_", "BothTwo_"].any (fun suffix =>
        match environment.find? (`UInt256Proof.Multiply |>.str s!"execute_limbs_{suffix}{index}") with
        | some (.thmInfo _) => true
        | _ => false) do continue
    let values ← listTerms call[4]!
    unless values.size == 3 do continue
    let left ← Term.exprToSyntax (← constructorArg ``CIL.Value.object values[0]!)
    let right ← Term.exprToSyntax (← constructorArg ``CIL.Value.object values[1]!)
    let out ← Term.exprToSyntax (← constructorArg ``CIL.Value.object values[2]!)
    let memory ← Term.exprToSyntax call[7]!
    let frame ← Term.exprToSyntax call[5]!
    let fuel ← Term.exprToSyntax call[1]!
    let number := Syntax.mkNumLit (toString index)
    for suffix in ["", "LeftTwo_", "BothTwo_"] do
      let summary := `UInt256Proof.Multiply |>.str s!"execute_limbs_{suffix}{index}"
      unless (← getEnv).contains summary do continue
      for (first, second, leftFact, rightFact) in [(a,b,leftReads,rightReads),(b,a,rightReads,leftReads)] do
        let saved ← saveState
        try
          let contract := mkIdent summary
          let final := mkIdent (← mkFreshUserName `limbProductMemory)
          let run := mkIdent (← mkFreshUserName `limbProductRun)
          let bytes := mkIdent (← mkFreshUserName `limbProductBytes)
          let adjustment := mkIdent (← mkFreshUserName `limbProductFuel)
          let domain ← `(term| by simp_all [BitVec.or_eq_zero_iff])
          let readsLeft ← `(term| by
            intro i
            try simp only [read64_write_local_byte, read64_initLocals_byte]
            exact $leftFact i)
          let readsRight ← `(term| by
            intro i
            try simp only [read64_write_local_byte, read64_initLocals_byte]
            exact $rightFact i)
          let mut arguments : Array Term := #[memory, left, right, out, frame,
            ← `(term| $fuel - executionBound Extracted.program $number), first, second]
          if suffix != "" then arguments := arguments.push domain
          if suffix == "BothTwo_" then arguments := arguments.push domain
          arguments := arguments.push readsLeft |>.push readsRight
          let mut applied : Term := contract
          for argument in arguments do
            applied ← `(term| $applied $argument)
          let proved := mkIdent (← mkFreshUserName `limbProductProof)
          evalTactic (← `(tactic| have $proved:ident := $applied))
          evalTactic (← `(tactic| obtain ⟨$final:ident, $run:ident, $bytes:ident⟩ := $proved:term))
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
  throwError "No applicable proved limb-product call"
end UInt256Proof.Multiply
