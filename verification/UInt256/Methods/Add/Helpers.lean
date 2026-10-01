import UInt256.Methods.Add.Automation
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof

if_extracted Extracted.addScalarUInt64Index {

-- Execute the common prefix once, then follow the generated conditional addresses.
-- The carry-specific contracts below reuse this checked execution result.
theorem execute_small_shared (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 (if a 0 + b < a 0 ∧ a 1 + 1 = 0 ∧ a 2 + 1 = 0 ∧ a 3 + 1 = 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (smallResult a b 0) (smallResult a b 1) (smallResult a b 2) (smallResult a b 3) (.byte address) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m base a hr
  cil_execute hr0, hr1, hr2, hr3 with (first | cil_store_call)
  all_goals intro address
  all_goals simp [*, smallResult, fin_val_three, store4]

theorem execute_small_no_carry (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hnc : ¬ a 0 + b < a 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) (a 1) (a 2) (a 3) (.byte address) := by
  obtain ⟨final, he, hm⟩ := execute_small_shared m base out frame fuel a b hr
  refine ⟨final, ?_, ?_⟩
  · simpa [hnc] using he
  · intro address
    simpa [smallResult, hnc, fin_val_three] using hm address

theorem execute_small_carry1 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) (a 1 + 1) (a 2) (a 3) (.byte address) := by
  change a 1 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h1
  obtain ⟨final, he, hm⟩ := execute_small_shared m base out frame fuel a b hr
  refine ⟨final, ?_, ?_⟩
  · simpa [hc, h1] using he
  · intro address
    simpa [smallResult, hc, h1, fin_val_three] using hm address

theorem execute_small_carry2 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 (a 2 + 1) (a 3) (.byte address) := by
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h2
  obtain ⟨final, he, hm⟩ := execute_small_shared m base out frame fuel a b hr
  refine ⟨final, ?_, ?_⟩
  · simpa [hc, h1, h2] using he
  · intro address
    simpa [smallResult, hc, h1, h2, fin_val_three] using hm address

theorem execute_small_carry3 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 = 0) (h3 : a 3 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 0 (a 3 + 1) (.byte address) := by
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h2
  change a 3 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h3
  obtain ⟨final, he, hm⟩ := execute_small_shared m base out frame fuel a b hr
  refine ⟨final, ?_, ?_⟩
  · simpa [hc, h1, h2, h3] using he
  · intro address
    simpa [smallResult, hc, h1, h2, h3, fin_val_three] using hm address

theorem execute_small_overflow (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 = 0) (h3 : a 3 + 1 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 1]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 0 0 (.byte address) := by
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h2
  change a 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h3
  obtain ⟨final, he, hm⟩ := execute_small_shared m base out frame fuel a b hr
  refine ⟨final, ?_, ?_⟩
  · simpa [hc, h1, h2, h3] using he
  · intro address
    simpa [smallResult, hc, h1, h2, h3, fin_val_three] using hm address

}

end UInt256Proof
