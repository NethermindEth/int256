import UInt256.ExecutionAutomation
import UInt256.Methods.Subtract.HelperContracts

open Lean Meta Elab Tactic
open CIL UInt256Model
namespace UInt256Proof

elab "cil_borrow_call" : tactic => withMainContext do
  unless (← getEnv).contains (Name.mkSimple "Extracted" |>.str "subtractWithBorrowIndex") &&
      (← getEnv).contains (Name.mkSimple "UInt256Proof" |>.str "execute_borrow_contract_at") do
    throwError "No proved summary available"
  let target ← getMainTarget
  let candidates := collectRuns target
  let mut selected : Option Expr := none
  for candidate in candidates do
    if candidate.hasLooseBVars then continue
    let args := candidate.getAppArgs
    if (← isDefEq args[2]! (mkConst (Name.mkSimple "Extracted" |>.str "subtractWithBorrowIndex"))) &&
        (← isDefEq args[3]! (mkNatLit 0)) then
      selected := some candidate
      break
  let some candidate := selected | throwError "No applicable proved borrow-helper call"
  if candidate.hasLooseBVars then
    throwError "Carry helper call still depends on an unresolved execution binder"
  let call := candidate.getAppArgs
  let values ← listTerms call[4]!
  unless values.size == 4 do throwError "Carry helper argument count changed"
  let x ← constructorArg ``CIL.Value.i64 values[0]!
  let y ← constructorArg ``CIL.Value.i64 values[1]!
  let ca ← constructorArg ``CIL.Value.ref values[2]!
  let ra ← constructorArg ``CIL.Value.ref values[3]!
  unless ca.isAppOfArity ``CIL.Address.local 2 && ra.isAppOfArity ``CIL.Address.local 2 do
    throwError "Carry contract requires caller-local references"
  let caArgs := ca.getAppArgs
  let raArgs := ra.getAppArgs
  unless ← isDefEq caArgs[0]! raArgs[0]! do
    throwError "Carry references occupy different caller frames"
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
      execute_borrow_contract_at $memory $frame $fuel $cslot $rslot $xTerm $yTerm _
        (by simp [*, write, initLocals]; all_goals rfl)
        (by omega)
        (by repeat first | apply borrow_bound | assumption | decide)
        (by simp [cil_code]; all_goals omega)))
  evalTactic (← `(tactic|
    have $hb:ident : ∀ address, $final (.byte address) = $memory (.byte address) := by
      intro address
      apply $hp
      all_goals simp))
  evalTactic (← `(tactic|
    have $hl:ident : ∀ index, index ≠ $cslot → index ≠ $rslot →
        $final (.local $frame index) = $memory (.local $frame index) := by
      intro index hborrow hsum
      apply $hp
      · intro other index hlower; intro h; have := Address.local.inj h; omega
      · simpa using hborrow
      · simpa using hsum))
  evalTactic (← `(tactic|
    have $hread:ident : ∀ base, read64 $final (.byte base) = read64 $memory (.byte base) := by
      intro base
      exact read64_congr $final $memory $hb base))
  evalTactic (← `(tactic| simp [cil_code, initLocals] at $hr:ident))
  evalTactic (← `(tactic| rw [$hr:ident]))
  evalTactic (← `(tactic| simp only [Option.bind_some]))

macro "cil_subtract_execute" facts:term,+ "with" calls:tacticSeq : tactic =>
  `(tactic| cil_execute_core borrow_expression, borrow_alternative_expression,
    borrow_flags_or, borrow_flags_add, borrow_bound, borrow_flag_fold, extend_subtract_choice, $[$facts:term],* with $calls:tacticSeq)

end UInt256Proof
