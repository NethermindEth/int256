import UInt256.Methods.Add.SmallAutomation
import UInt256.RepresentationLemmas
import UInt256.Methods.Reporting.Arithmetic

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Reporting

if_extracted Extracted.addScalarIndex {

theorem execute_scalar_general (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hna : a 1 ||| a 2 ||| a 3 ≠ 0) (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex)
      Extracted.addScalarIndex 0 [.object left, .object right, .object out, .i32 1]
      frame [] m = some (final, [.i32 (if finalCarry a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = (store4 m out (a 0 + b 0)
        (a 1 + b 1 + carry (a 0) (b 0) 0)
        (a 2 + b 2 + carry (a 1) (b 1) (carry (a 0) (b 0) 0))
        (a 3 + b 3 + carry (a 2) (b 2) (carry (a 1) (b 1) (carry (a 0) (b 0) 0)))) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  change a 1 ||| a 2 ||| a 3 ≠ BitVec.ofNat 64 0 at hna
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hnb
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hna, hnb,
    finalCarry, FeatureProfile.evaluate, word_positive,
    show (1 : W32) = BitVec.ofNat 32 1 from rfl
  intro address
  cil_preserved_store
  intro location
  simp [*, write]


theorem execute_scalar_general_at (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hna : a 1 ||| a 2 ||| a 3 ≠ 0) (hnb : b 1 ||| b 2 ||| b 3 ≠ 0)
    (hf : executionBound Extracted.program Extracted.addScalarIndex ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 1] frame [] m =
        some (final, [.i32 (if finalCarry a b ≠ 0 then 1 else 0)]) ∧
      ∀ address, final (.byte address) = store4 m out
        (sumWords a b 0) (sumWords a b 1) (sumWords a b 2) (sumWords a b 3) (.byte address) := by
  obtain ⟨final, hr, hm⟩ := execute_scalar_general m left right out frame 0 a b ha hb hna hnb
  simp only [Nat.zero_add] at hr
  exact ⟨final, run_of_le _ _ _ _ _ _ _ _ _ _ hf hr, by simpa (config := { implicitDefEqProofs := false }) [sumWords, fin_val_three] using hm⟩


#print axioms UInt256Proof.Reporting.execute_scalar_general
}

end UInt256Proof.Reporting
