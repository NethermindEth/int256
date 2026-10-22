import Extracted
import UInt256.Methods.Subtract.WrappingSafety
import UInt256.Methods.Subtract.BorrowContract

namespace UInt256Proof.Subtract.FixtureExtractedHelper
open CIL.Safety UInt256Proof.Subtract.Safety UInt256Proof.Subtract.Profile

/-- The borrow helper's difference is a call to a private pure helper. -/
theorem helper_run :
    BorrowRun Extracted.program Extracted.subtractWithBorrowIndex Extracted.subtractWithBorrowBody borrowWord := by
  borrow_run_steps [borrowWord, BitVec.toNat_or, BitVec.toNat_and]

theorem correctness : UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  checked_wrapping_contract (borrow_contract_of_run borrowWord rfl ⟨rfl, rfl, rfl, rfl⟩ helper_run borrowWord_correct)

#print axioms correctness
end UInt256Proof.Subtract.FixtureExtractedHelper
