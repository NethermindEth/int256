import UInt256.Methods.Add.SmallAutomation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

if_extracted Extracted.addScalarIndex {

theorem execute_scalar_right_small_words (m : Memory) (left right out frame fuel : Nat)
    (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 0) :
    ∃ final flag, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex) Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (store4 m out (smallResult a (b 0) 0) (smallResult a (b 0) 1) (smallResult a (b 0) 2) (smallResult a (b 0) 3)) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, h1, h2, h3
    with (first | cil_small_call | cil_carry_call | cil_store_call)
  intro address
  apply store4_bytes _ _ ?_ _ _ _ _ _ address
  intro location
  simp [*, write]

theorem execute_scalar_left_small_words (m : Memory) (left right out frame fuel : Nat)
    (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hn : b 1 ||| b 2 ||| b 3 ≠ 0)
    (h1 : a 1 = 0) (h2 : a 2 = 0) (h3 : a 3 = 0) :
    ∃ final flag, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex) Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (store4 m out (smallResult b (a 0) 0) (smallResult b (a 0) 1) (smallResult b (a 0) 2) (smallResult b (a 0) 3)) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hn
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hn, h1, h2, h3
    with (first | cil_small_call | cil_carry_call | cil_store_call)
  intro address
  apply store4_bytes _ _ ?_ _ _ _ _ _ address
  intro location
  simp [*, write]


}

end UInt256Proof
