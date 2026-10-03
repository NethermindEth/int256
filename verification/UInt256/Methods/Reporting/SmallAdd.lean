import UInt256.Methods.Add.Helpers
import UInt256.Methods.Reporting.Arithmetic

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

if_extracted Extracted.addScalarUInt64Index {

theorem execute_small_report_at (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hf : executionBound Extracted.program Extracted.addScalarUInt64Index ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final,
        [.i32 (if 2^256 ≤ (value a).toNat + (value (singleLimb b)).toNat then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (smallResult a b 0) (smallResult a b 1) (smallResult a b 2) (smallResult a b 3) (.byte address) := by
  obtain ⟨final, he, hm⟩ := execute_small_shared m base out frame 0 a b hr
  refine ⟨final, ?_, hm⟩
  have execution := run_of_le _ _ _ _ _ _ _ _ _ _ hf he
  simpa only [small_overflow_iff] using execution


#print axioms UInt256Proof.Reporting.execute_small_report_at
}

end UInt256Proof.Reporting
