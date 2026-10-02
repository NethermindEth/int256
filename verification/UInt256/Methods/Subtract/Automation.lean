import UInt256.ExecutionAutomation
import UInt256.Methods.Subtract.HelperContracts

open Lean Meta Elab Tactic
open CIL UInt256Model
namespace UInt256Proof

elab "cil_borrow_call" : tactic => withMainContext do
  wordHelperCall `Extracted.subtractWithBorrowIndex `UInt256Proof.execute_borrow_contract_at
    "borrow" (mkIdent ``borrow_bound) (← `(tactic| (simp [*, write, initLocals]; all_goals rfl)))

macro "cil_subtract_execute" facts:term,+ "with" calls:tacticSeq : tactic =>
  `(tactic| cil_execute_core borrow_expression, borrow_alternative_expression, borrow_alternative_or_expression,
    borrow_flags_or, borrow_flags_add, borrow_flags_alternative_or, borrow_bound, borrow_flag_fold,
    extend_subtract_choice, $[$facts:term],* with $calls:tacticSeq)

end UInt256Proof
