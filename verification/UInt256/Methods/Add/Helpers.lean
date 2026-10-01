import UInt256.Methods.Add.HelperContracts

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

if_extracted Extracted.addScalarUInt64Index {

theorem execute_small_no_carry (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hnc : ¬ a 0 + b < a 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) (a 1) (a 2) (a 3) (.byte address) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m base a hr
  cil_steps write_local_read_local, hr0, hr1, hr2, hr3, hnc
  simp [store4]
  all_goals intro address; rfl

theorem execute_small_carry1 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) (a 1 + 1) (a 2) (a 3) (.byte address) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m base a hr
  change a 1 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h1
  cil_steps write_local_read_local, hr0, hr1, hr2, hr3, hc, h1
  simp [store4]
  all_goals intro address; rfl

theorem execute_small_carry2 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 (a 2 + 1) (a 3) (.byte address) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m base a hr
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h2
  cil_steps write_local_read_local, hr0, hr1, hr2, hr3, hc, h1, h2
  simp [store4]
  all_goals intro address; rfl

theorem execute_small_carry3 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 = 0) (h3 : a 3 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 0 (a 3 + 1) (.byte address) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m base a hr
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h2
  change a 3 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h3
  cil_steps write_local_read_local, hr0, hr1, hr2, hr3, hc, h1, h2, h3
  simp [store4]
  all_goals intro address; rfl

theorem execute_small_overflow (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 = 0) (h3 : a 3 + 1 = 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarUInt64Index) Extracted.addScalarUInt64Index 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 1]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 0 0 (.byte address) := by
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m base a hr
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h2
  change a 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h3
  cil_steps write_local_read_local, hr0, hr1, hr2, hr3, hc, h1, h2, h3
  simp [store4]
  all_goals intro address; rfl
}

end UInt256Proof
