import UInt256.Methods.Add.VectorRepairContract
import UInt256.Methods.Add.VectorParentCascadeMath

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model CIL.Vector

/-- The checked helper invocation repairs the saved lane sum to mathematical
    addition. The wrapping parent discards the helper's scalar flag. -/
theorem checked_repair_sum (memory : Memory) (output : Reference) (a b : Limbs)
    (call : CallingConditions Extracted.program memory [] [output]) :
    ∃ fuel final flag,
      InvocationCertificate Extracted.program repairIndex
        (repairArguments (zip256 (· + ·) (value a) (value b))
          (generatedCarry (value a) (value b))
          (propagationMask (zip256 (· + ·) (value a) (value b))) output)
        memory fuel final [.scalar (.i32 flag)] ∧
      read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  obtain ⟨fuel, final, certificate, result, writable, footprint⟩ := checked_repair_contract memory output
    (zip256 (· + ·) (value a) (value b)) (generatedCarry (value a) (value b))
    (propagationMask (zip256 (· + ·) (value a) (value b))) call
  rw [vector_cascade_sum a b] at result
  exact ⟨fuel, final, _, certificate, result, writable, footprint⟩

#print axioms checked_repair_sum
end UInt256Proof.Add.Safety
