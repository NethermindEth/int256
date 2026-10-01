import CIL.SymbolicExecution
open Lean Elab Command
namespace SummaryTransactions

def candidate : Nat := 0
def marker (n : Nat) := n + 1

if_extracted SummaryTransactions.candidate {
  @[cil_code] theorem tentative (n : Nat) : marker n = n + 1 := rfl
  theorem invalid : False := by decide
}
run_cmd do
  for name in [`SummaryTransactions.tentative, `SummaryTransactions.invalid] do
    if (← getEnv).contains name then throwError "Failed summary leaked {name}"
-- A leaked simp registration would still reference the removed theorem.
example : marker 2 = 3 := by simp only [cil_code, marker]

if_extracted SummaryTransactions.candidate {
  theorem admitted : False := by sorry
}
run_cmd do
  if (← getEnv).contains `SummaryTransactions.admitted then
    throwError "Admitted summary survived"

if_extracted SummaryTransactions.candidate {
  axiom assumed : False
}
run_cmd do
  if (← getEnv).contains `SummaryTransactions.assumed then
    throwError "Assumed summary survived"

if_extracted SummaryTransactions.candidate {
  theorem accepted : marker 2 = 3 := rfl
}
run_cmd do
  unless (← getEnv).contains `SummaryTransactions.accepted do
    throwError "Proved summary was discarded"
#print axioms accepted
end SummaryTransactions
