import UInt256.Methods.Add.Helpers

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem store4_shape (m : Memory) (out : Nat) (a : Limbs) (b r0 r1 r2 r3 : W64)
    (hs : (fun i : Fin 4 => if i.val = 0 then r0 else if i.val = 1 then r1 else
      if i.val = 2 then r2 else r3) = smallResult a b) :
    store4 m out r0 r1 r2 r3 = writeBytes m out (value (smallResult a b)).toNat 32 := by
  rw [store4_value, hs]

theorem execute_small (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i))) :
    ∃ final flag, run Extracted.program (fuel + 200) 2 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (writeBytes m out
        (value a + value (singleLimb b)).toNat 32) (.byte address) := by
  rw [← small_result_sum]
  by_cases hc : a 0 + b < a 0
  · by_cases h1 : a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
    · by_cases h2 : a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
      · by_cases h3 : a 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
        · obtain ⟨final, he, hm⟩ := execute_small_overflow m base out frame fuel a b hr hc h1 h2 h3
          refine ⟨final, 1, he, ?_⟩
          intro address
          rw [hm, store4_shape m out a b (a 0+b) 0 0 0
            (by funext i; simp [smallResult, hc, h1, h2, h3])]
        · obtain ⟨final, he, hm⟩ := execute_small_carry3 m base out frame fuel a b hr hc h1 h2 h3
          refine ⟨final, 0, he, ?_⟩
          intro address
          rw [hm, store4_shape m out a b (a 0+b) 0 0 (a 3+1)
            (by funext i; simp [smallResult, hc, h1, h2])]
      · obtain ⟨final, he, hm⟩ := execute_small_carry2 m base out frame fuel a b hr hc h1 h2
        refine ⟨final, 0, he, ?_⟩
        intro address
        rw [hm, store4_shape m out a b (a 0+b) 0 (a 2+1) (a 3)
          (by funext i; simp [smallResult, hc, h1, h2])]
    · obtain ⟨final, he, hm⟩ := execute_small_carry1 m base out frame fuel a b hr hc h1
      refine ⟨final, 0, he, ?_⟩
      intro address
      rw [hm, store4_shape m out a b (a 0+b) (a 1+1) (a 2) (a 3)
        (by funext i; simp [smallResult, hc, h1])]
  · obtain ⟨final, he, hm⟩ := execute_small_no_carry m base out frame fuel a b hr hc
    refine ⟨final, 0, he, ?_⟩
    intro address
    rw [hm, store4_shape m out a b (a 0+b) (a 1) (a 2) (a 3)
      (by funext i; simp [smallResult, hc])]

end UInt256Proof
