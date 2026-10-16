import UInt256.Methods.Add.CarryMemory
import UInt256.Methods.Add.CarryContract

namespace UInt256Proof.Safety

/-- The production helper's checked contract, supplied to the shared parent proofs. -/
theorem carry_checked_contract : CarryHelperContract :=
  carry_contract_of_run carryWord carry_run_of_memory_steps carryWord_correct

#print axioms carry_checked_contract

end UInt256Proof.Safety
