import UInt256.Methods.Add.CarryPost

namespace UInt256Proof.Safety

open CIL.Safety

/-- Symbolic execution of the extracted body, with explicit checked memory
    transitions. Access and preservation lemmas discharge these premises. -/
theorem carry_run_of_memory_steps : CarryRun carryWord := by
  carry_run_steps [carryWord, BitVec.toNat_add]

#print axioms carry_run_of_memory_steps

end UInt256Proof.Safety
