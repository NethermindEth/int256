import UInt256.Methods.Subtract.SIMD128
import UInt256.Methods.Reporting.Arithmetic

open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Reporting

if_extracted Extracted.subtractVector128Index {
theorem execute_subtract128_report_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hf : executionBound Extracted.program Extracted.subtractVector128Index ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.subtractVector128Index 0
      [.object left, .object right, .object out] frame [] m =
        some (final, [.i32 (if finalBorrow a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (differenceWords a b 0) (differenceWords a b 1)
        (differenceWords a b 2) (differenceWords a b 3) (.byte address) := by
  obtain ⟨final, hr, hm⟩ := execute_subtract128 m left right out frame 0 a b ha hb
  simp only [Nat.zero_add] at hr
  refine ⟨final, ?_, hm⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf hr
}
end UInt256Proof.Reporting
