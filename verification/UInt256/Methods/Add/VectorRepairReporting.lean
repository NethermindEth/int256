import UInt256.Methods.Add.VectorRepairContract
import UInt256.Methods.Add.VectorCarryFlags

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model CIL.Vector

/-- Repair invocation proves both the modular sum and exact mathematical
    overflow, over the same saved initial operands and checked execution. -/
theorem checked_repair_reporting (memory : Memory) (output : Reference) (a b : Limbs)
    (call : CallingConditions Extracted.program memory [] [output]) :
    ∃ fuel final,
      InvocationCertificate Extracted.program repairIndex
        (repairArguments (zip256 (· + ·) (value a) (value b))
          (generatedCarry (value a) (value b))
          (propagationMask (zip256 (· + ·) (value a) (value b))) output)
        memory fuel final [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))] ∧
      read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  obtain ⟨fuel, final, certificate, result, writable, footprint⟩ := checked_repair_contract memory output
    (zip256 (· + ·) (value a) (value b)) (generatedCarry (value a) (value b))
    (propagationMask (zip256 (· + ·) (value a) (value b))) call
  rw [vector_cascade_sum a b] at result
  rw [vector_cascade_overflow a b] at certificate
  exact ⟨fuel, final, certificate, result, writable, footprint⟩

#print axioms checked_repair_reporting
end UInt256Proof.Add.Safety
