import UInt256.Methods.Subtract.BorrowFrameless

namespace UInt256Proof.Subtract.Safety
open CIL.Safety

theorem borrow_run : BorrowRun borrowWord := by
  borrow_run_steps [borrowWord, BitVec.toNat_or, BitVec.toNat_and]

/-- The production helper's checked contract, supplied to the shared parent proofs. -/
theorem borrow_checked_contract : BorrowHelperContract :=
  borrow_contract_of_run borrowWord borrow_run borrowWord_correct

#print axioms borrow_run
#print axioms borrow_checked_contract
end UInt256Proof.Subtract.Safety
