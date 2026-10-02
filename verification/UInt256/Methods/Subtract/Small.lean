import UInt256.Methods.Subtract.Automation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof

if_extracted Extracted.subtractScalarUInt64Index {

theorem execute_subtract_small (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.subtractScalarUInt64Index)
      Extracted.subtractScalarUInt64Index 0 [.object base, .i64 b, .object out] frame [] m =
        some (final, [.i32 (if a 0 < b ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (smallDifference a b 0) (smallDifference a b 1)
        (smallDifference a b 2) (smallDifference a b 3) (.byte address) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m base a hr
  cil_subtract_execute hr0, hr1, hr2, hr3 with (first | cil_store_call)
  all_goals intro address
  all_goals simp [*, smallDifference, fin_val_three, store4]

theorem execute_subtract_small_at (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hf : executionBound Extracted.program Extracted.subtractScalarUInt64Index ≤ fuel) :
    ∃ final flag, run Extracted.program fuel Extracted.subtractScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = store4 m out
        (smallDifference a b 0) (smallDifference a b 1)
        (smallDifference a b 2) (smallDifference a b 3) (.byte address) := by
  obtain ⟨final, he, hm⟩ := execute_subtract_small m base out frame 0 a b hr
  refine ⟨final, (if a 0 < b ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 then 1 else 0), ?_, hm⟩
  exact run_of_le _ _ _ _ _ _ _ _ _ _ hf he

}
end UInt256Proof
