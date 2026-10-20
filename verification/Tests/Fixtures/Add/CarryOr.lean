import Extracted
import UInt256.Methods.Add.EntrySafety
import UInt256.Methods.Add.CarryContract

namespace UInt256Proof.Add.FixtureCarryOr
open CIL.Safety UInt256Proof.Safety UInt256Proof.Add.CarrySafety

/-- The fixture joins the two carry indicators with `or` instead of `+`. -/
def carryOrWord (a b c : BitVec 64) : BitVec 64 :=
  ((if a + b < a then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64) |||
  ((if a + b + c < a + b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

theorem carry_or_run : CarryRun Extracted.program Extracted.addWithCarryIndex Extracted.addWithCarryBody carryOrWord := by
  carry_run_steps [carryOrWord, BitVec.toNat_or]

theorem correctness : UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program 0 :=
  checked_add_contract (carry_contract_of_run carryOrWord rfl ⟨rfl, rfl, rfl, rfl⟩ carry_or_run fun a b c incoming => by
    simp only [carryOrWord, UInt256Proof.extend_choice]
    exact UInt256Proof.carry_or_expression a b c incoming)

#print axioms correctness
end UInt256Proof.Add.FixtureCarryOr
