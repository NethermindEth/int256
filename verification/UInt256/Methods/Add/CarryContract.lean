import UInt256.Methods.Add.CarryInvoke
import CIL.Safety.ExecutionStaticWorld

namespace UInt256Proof.Safety

open CIL.Safety

/-- A two-local carry body with a proved run and a carry word equal to the
    mathematical carry for incoming carries of at most one. -/
theorem carry_contract_of_run (cw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) (runs : CarryRun cw)
    (correct : ∀ a b c : BitVec 64, c.toNat ≤ 1 → cw a b c = UInt256Proof.carry a b c) :
    CarryHelperContract := by
  intro a b c carryRef output memory wellFormed incoming carryReadable carryWritable outputWritable disjoint
  obtain ⟨fuel, result, invoked, _, _, footprint, retainedAccess, outputBytes, carryBytes⟩ :=
    carry_invoke_succeeds cw runs a b c carryRef output memory wellFormed carryReadable carryWritable outputWritable
  have carryBytes := carryBytes disjoint
  rw [correct a b c incoming] at carryBytes
  exact ⟨fuel, result, invoked,
    ⟨invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked,
      outputBytes, carryBytes, UInt256Proof.carry_bound a b c incoming,
      UInt256Proof.carry_word_nat a b c incoming, footprint, retainedAccess,
      fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩⟩

#print axioms carry_contract_of_run

end UInt256Proof.Safety
