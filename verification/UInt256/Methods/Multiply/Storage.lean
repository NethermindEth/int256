import UInt256.ExecutionAutomation
import UInt256.VectorRepresentation
open Lean Meta Elab Command Tactic CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

@[simp↓] theorem eval_create256 (r0 r1 r2 r3 : W64) :
    evalIntrinsic (.vector (.create64 256)) [.i64 r0, .i64 r1, .i64 r2, .i64 r3] =
      some (.v256 (CIL.Vector.pack256 r0 r1 r2 r3)) := by rfl

@[simp↓] theorem eval_store256 (memory : Memory) (out : Nat) (r0 r1 r2 r3 : W64)
    (rest : List Value) :
    evalMemory .store256 (.v256 (CIL.Vector.pack256 r0 r1 r2 r3) :: .ref (.byte out) :: rest) memory =
      some (store4 memory out r0 r1 r2 r3, rest) := by
  simp only [evalMemory, write256_four_limbs, bind, pure, Option.bind]

elab "multiply_storage_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.storageCandidates)
  for expression in indices do
    let expression ← liftTermElabM do whnf expression
    let .lit (.natVal index) := expression | throwError "Expected a concrete storage candidate"
    let number := Syntax.mkNumLit (toString index)
    let theoremName := mkIdent (Name.mkSimple s!"execute_storage_{index}")
    let candidates := mkIdent `Extracted.storageCandidates
    elabCommand (← `(command| if_extracted $candidates {
      theorem $theoremName (memory : Memory) (frame fuel out : Nat)
          (r0 r1 r2 r3 : W64)
          (bound : executionBound Extracted.program $number ≤ fuel) :
          ∃ final, run Extracted.program fuel $number 0
            [.object out, .i64 r0, .i64 r1, .i64 r2, .i64 r3] frame [] memory = some (final, []) ∧
            (∀ address, final (.byte address) = store4 memory out r0 r1 r2 r3 (.byte address)) ∧
            ∀ other index, other ≠ frame → final (.local other index) = memory (.local other index) := by
        have splitFuel : fuel = (fuel - executionBound Extracted.program $number) +
            executionBound Extracted.program $number := by omega
        rw [splitFuel]
        generalize fuel - executionBound Extracted.program $number = remaining
        cil_execute_core evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue with
          (fail "Use raw storage instructions")
        all_goals simp [store4]
        all_goals intro address
        all_goals rfl
    }))

multiply_storage_summaries

elab "cil_multiply_store_call" : tactic => withMainContext do
  for expression in collectRuns (← getMainTarget) do
    if expression.hasLooseBVars then continue
    let call := expression.getAppArgs
    unless ← isDefEq call[3]! (mkNatLit 0) do continue
    let .lit (.natVal index) ← whnf call[2]! | continue
    let summary := `UInt256Proof.Multiply |>.str s!"execute_storage_{index}"
    unless (← getEnv).contains summary do continue
    let values ← listTerms call[4]!
    unless values.size == 5 do continue
    let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
    let mut words : Array Term := #[]
    for value in values[1:] do
      words := words.push (← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 value))
    let contract := mkIdent summary
    let memory ← PrettyPrinter.delab call[7]!
    let frame ← PrettyPrinter.delab call[5]!
    let fuel ← PrettyPrinter.delab call[1]!
    let final := mkIdent (← mkFreshUserName `productMemory)
    let run := mkIdent (← mkFreshUserName `productStoreRun)
    let bytes := mkIdent (← mkFreshUserName `productStoreBytes)
    let locals := mkIdent (← mkFreshUserName `productStoreLocals)
    let r0 := words[0]!
    let r1 := words[1]!
    let r2 := words[2]!
    let r3 := words[3]!
    evalTactic (← `(tactic|
      obtain ⟨$final:ident, $run:ident, $bytes:ident, $locals:ident⟩ :=
        $contract $memory $frame $fuel $out $r0 $r1 $r2 $r3
          (by simp [cil_code]; all_goals omega)))
    rewriteHelperRun run
    return
  throwError "No proved multiplication storage call"
end UInt256Proof.Multiply
