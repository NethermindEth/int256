import UInt256.Methods.Subtract.Bindings
import UInt256.Methods.Subtract.BorrowContract

namespace UInt256Proof.Subtract.Safety
open UInt256Proof.Subtract.Profile

/-- The extracted helper is the production borrow body, supplied to the shared parent proofs. -/
theorem borrow_production_contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex :=
  borrow_helper_contract (profile := Extracted.profile) rfl

#print axioms borrow_production_contract
end UInt256Proof.Subtract.Safety
