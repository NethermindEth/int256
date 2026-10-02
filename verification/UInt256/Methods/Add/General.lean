import UInt256.Methods.Add.Automation
import UInt256.RepresentationLemmas
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof

if_extracted Extracted.addScalarIndex {

-- Formal execution follows the generated code; arithmetic is proved separately.
theorem execute_scalar_general_words (m : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (ha : ∀ i : Fin 4, read64 m (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (hb : ∀ i : Fin 4, read64 m (.byte (right + 8*i.val)) = some (.i64 (b i)))
    (hna : a 1 ||| a 2 ||| a 3 ≠ 0) (hnb : b 1 ||| b 2 ||| b 3 ≠ 0) :
    ∃ final flag, run Extracted.program (fuel + executionBound Extracted.program Extracted.addScalarIndex) Extracted.addScalarIndex 0
      [.object left, .object right, .object out, .i32 0] frame [] m = some (final, [.i32 flag]) ∧
      ∀ address, final (.byte address) = (store4 m out (a 0 + b 0)
        (a 1 + b 1 + carry (a 0) (b 0) 0)
        (a 2 + b 2 + carry (a 1) (b 1) (carry (a 0) (b 0) 0))
        (a 3 + b 3 + carry (a 2) (b 2) (carry (a 1) (b 1) (carry (a 0) (b 0) 0)))) (.byte address) := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := limb_reads m left a ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := limb_reads m right b hb
  change a 1 ||| a 2 ||| a 3 ≠ BitVec.ofNat 64 0 at hna
  change b 1 ||| b 2 ||| b 3 ≠ BitVec.ofNat 64 0 at hnb
  cil_execute ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hna, hnb
  intro address
  cil_preserved_store
  intro location
  simp [*, write]

}

end UInt256Proof
