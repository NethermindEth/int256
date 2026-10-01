import UInt256.Methods.Add.Small

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem execute_scalar_right_small (m : Memory) (left right out frame fuel : Nat)
    (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 0) :
    ∃ final flag, run Extracted.program (fuel + 300) 1 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  let child := initLocals (write m (.local frame 0) (.i64 (b 0))) (frame+1) Extracted.method2.locals
  have hread : ∀ i : Fin 4, read64 child (.byte (left + 8*i.val)) = some (.i64 (a i)) := by
    intro i
    simp [child, ha]
  obtain ⟨final, flag, he, hm⟩ := execute_small child left out (frame+1) (fuel+82) a (b 0) hread
  have hf : fuel + 82 + 200 = fuel + 282 := by omega
  rw [hf] at he
  simp [Extracted.program, Extracted.method1, child] at he
  obtain ⟨hr0, hr1, hr2, hr3⟩ := limb_reads m right b hb
  refine ⟨final, flag, ?_, ?_⟩
  · iterate 18
      rw [run]
      simp [step, Extracted.program, Extracted.method1, binary, truth,
        write_local_read_local, show (3 : Fin 4).val = 3 from rfl,
        hr0, hr1, hr2, hr3, h1, h2, h3]
    rw [he]
    simp only [Option.bind_some]
    rw [run]
    simp [step]
  · have hs := singleLimb_eq b h1 h2 h3
    rw [hs] at hm
    intro address
    rw [hm]
    apply writeBytes_congr child m (by intro location; simp [child, initLocals_bytes])

theorem execute_scalar_left_small (m : Memory) (left right out frame fuel : Nat)
    (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hn : b 1 ||| b 2 ||| b 3 ≠ 0)
    (h1 : a 1 = 0) (h2 : a 2 = 0) (h3 : a 3 = 0) :
    ∃ final flag, run Extracted.program (fuel + 300) 1 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  let child := initLocals (write (write m (.local frame 0) (.i64 (b 0)))
    (.local frame 1) (.i64 (a 0))) (frame+1) Extracted.method2.locals
  have hread : ∀ i : Fin 4, read64 child (.byte (right + 8*i.val)) = some (.i64 (b i)) := by
    intro i
    simp [child, hb]
  obtain ⟨final, flag, he, hm⟩ := execute_small child right out (frame+1) (fuel+70) b (a 0) hread
  have hf : fuel + 70 + 200 = fuel + 270 := by omega
  rw [hf] at he
  simp [Extracted.program, Extracted.method1, child] at he
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hn
  refine ⟨final, flag, ?_, ?_⟩
  · iterate 30
      rw [run]
      simp [step, Extracted.program, Extracted.method1, binary, truth,
        write_local_read_local, show (3 : Fin 4).val = 3 from rfl,
        ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hn, h1, h2, h3]
    rw [he]
    simp only [Option.bind_some]
    rw [run]
    simp [step]
  · have hs := singleLimb_eq a h1 h2 h3
    rw [hs, BitVec.add_comm] at hm
    intro address
    rw [hm]
    apply writeBytes_congr child m (by intro location; simp [child, initLocals_bytes])

theorem execute_scalar_general (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hna : a 1 ||| a 2 ||| a 3 ≠ 0) (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final flag, run Extracted.program (fuel + 300) 1 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  let c1 := carry (a 0) (b 0) 0
  let c2 := carry (a 1) (b 1) c1
  let c3 := carry (a 2) (b 2) c2
  let c4 := carry (a 3) (b 3) c3
  let m0 := write (write (write m (.local frame 0) (.i64 (b 0)))
    (.local frame 1) (.i64 (a 0))) (.local frame 2) (.i64 0)
  let m1 := carryState m0 frame 3 (a 0) (b 0) 0
  let m2 := carryState m1 frame 4 (a 1) (b 1) c1
  let m3 := carryState m2 frame 5 (a 2) (b 2) c2
  let m4 := carryState m3 frame 6 (a 3) (b 3) c3
  have he1 := execute_parent_carry m0 frame 3 (fuel+264) (a 0) (b 0) 0
    (by omega) (by simp [m0, write_local_read_local])
  have he2 := execute_parent_carry m1 frame 4 (fuel+257) (a 1) (b 1) c1
    (by omega) (by simp [m1, c1])
  have he3 := execute_parent_carry m2 frame 5 (fuel+250) (a 2) (b 2) c2
    (by omega) (by simp [m2, c2])
  have he4 := execute_parent_carry m3 frame 6 (fuel+243) (a 3) (b 3) c3
    (by omega) (by simp [m3, c3])
  have hs := execute_store_at m4 out (frame+1) (fuel+237)
    (a 0+b 0) (a 1+b 1+c1) (a 2+b 2+c2) (a 3+b 3+c3) (by omega)
  simp [Extracted.program, Extracted.method1, m0] at he1
  simp [Extracted.program, Extracted.method1, m1, m0, c1] at he2
  simp [Extracted.program, Extracted.method1, m2, m1, m0, c2, c1] at he3
  simp [Extracted.program, Extracted.method1, m3, m2, m1, m0, c3, c2, c1] at he4
  simp [Extracted.program, Extracted.method1, m4, m3, m2, m1, m0, c3, c2, c1] at hs
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  change a 1 ||| a 2 ||| a 3 ≠ BitVec.ofNat 64 0 at hna
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hnb
  refine ⟨store4 m4 out (a 0+b 0) (a 1+b 1+c1) (a 2+b 2+c2) (a 3+b 3+c3),
    (if c4 > 0 then 1 else 0), ?_, ?_⟩
  · iterate 36
      rw [run]
      simp [step, Extracted.program, Extracted.method1, binary, truth,
        write_local_read_local, show (3 : Fin 4).val = 3 from rfl,
        ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hna, hnb]
    rw [he1]
    simp only [Option.bind_some]
    iterate 7
      rw [run]
      simp [step, binary, truth, ha1, hb1]
    rw [he2]
    simp only [Option.bind_some]
    iterate 7
      rw [run]
      simp [step, binary, truth, ha2, hb2]
    rw [he3]
    simp only [Option.bind_some]
    iterate 7
      rw [run]
      simp [step, binary, truth, show (3 : Fin 4).val = 3 from rfl, ha3, hb3]
    rw [he4]
    simp only [Option.bind_some]
    iterate 6
      rw [run]
      simp [step, binary, truth, show Extracted.method4.locals = [] from rfl, initLocals]
    rw [hs]
    simp only [Option.bind_some]
    iterate 5
      rw [run]
      simp [step, binary, truth, m4, m3, m2, m1, m0, c4, c3, c2, c1]
  · have hm : ∀ address, m4 (.byte address) = m (.byte address) := by
      intro address
      simp [m4, m3, m2, m1, m0]
    intro address
    rw [store4_bytes m4 m hm, store4_value]
    have hv := four_limb_sum a b
    dsimp only at hv
    rw [hv]

theorem execute_scalar (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final flag, run Extracted.program (fuel + 300) 1 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out (value a + value b).toNat 32) (.byte address) := by
  by_cases hnb : b 1 ||| b 2 ||| b 3 = BitVec.ofNat 64 0
  · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hnb
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
    exact execute_scalar_right_small m left right out frame fuel a b ha hb h1 h2 h3
  · by_cases hna : a 1 ||| a 2 ||| a 3 = BitVec.ofNat 64 0
    · obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp hna
      obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
      exact execute_scalar_left_small m left right out frame fuel a b ha hb hnb h1 h2 h3
    · exact execute_scalar_general m left right out frame fuel a b ha hb hna hnb

end UInt256Proof
