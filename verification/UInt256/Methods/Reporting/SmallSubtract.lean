import UInt256.Methods.Subtract.Small
import UInt256.Methods.Reporting.Arithmetic

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

if_extracted Extracted.subtractScalarUInt64Index {

theorem execute_subtract_small_report_at (m : Memory) (base out frame fuel : Nat)
    (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hf : executionBound Extracted.program Extracted.subtractScalarUInt64Index ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.subtractScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final,
        [.i32 (if (value a).toNat < (value (singleLimb b)).toNat then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (smallDifference a b 0) (smallDifference a b 1)
        (smallDifference a b 2) (smallDifference a b 3) (.byte address) := by
  obtain ⟨final, he, hm⟩ := execute_subtract_small m base out frame 0 a b hr
  refine ⟨final, ?_, hm⟩
  have execution := run_of_le _ _ _ _ _ _ _ _ _ _ hf he
  simpa only [small_underflow_iff] using execution

#print axioms execute_subtract_small_report_at
}

end UInt256Proof.Reporting
