import Extracted
import UInt256.Methods.Add.EntrySafety
import UInt256.Methods.Add.CarryContract

namespace UInt256Proof.Add.FixtureExtractedHelper
open CIL.Safety UInt256Proof.Safety UInt256Proof.Add.CarrySafety

/-- The carry helper's first sum is a call to a private pure helper. -/
theorem helper_run : CarryRun Extracted.program Extracted.addWithCarryIndex Extracted.addWithCarryBody carryWord := by
  carry_run_steps [carryWord, BitVec.toNat_add]

theorem correctness : UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  checked_add_contract (carry_contract_of_run carryWord rfl ⟨rfl, rfl, rfl, rfl⟩ helper_run carryWord_correct)

#print axioms correctness
end UInt256Proof.Add.FixtureExtractedHelper
