import UInt256.ExecutionAutomation
import UInt256.Methods.Add.HelperContracts

open Lean Meta Elab Tactic
open CIL UInt256Model
namespace UInt256Proof

elab "cil_carry_call" : tactic => withMainContext do
  wordHelperCall `Extracted.addWithCarryIndex `UInt256Proof.execute_carry_contract_at
    "carry" (mkIdent ``carry_bound) (← `(tactic| (simp_all [write, initLocals]; all_goals rfl)))

theorem carry_flag_fold (x y : W64) :
    (if x + y < x then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) =
      carry x y (BitVec.ofNat 64 0) := (carry_zero x y).symm

macro "cil_execute" facts:term,+ "with" calls:tacticSeq : tactic =>
  `(tactic| cil_execute_core carry_expression, carry_or_expression, carry_flags_add,
    carry_flags_or, carry_bound, carry_flag_fold, $[$facts:term],* with $calls:tacticSeq)

macro "cil_execute" facts:term,+ : tactic =>
  `(tactic| cil_execute $[$facts:term],* with (first | cil_carry_call | cil_store_call))

end UInt256Proof
