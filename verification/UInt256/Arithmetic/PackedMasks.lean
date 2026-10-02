import UInt256.Arithmetic.Cascade
import UInt256.LookupTable
import CIL.SIMD.AVX

open CIL CIL.Vector

namespace UInt256Proof.SIMD

def packedFlags (b0 b1 b2 b3 : Bool) : W32 :=
  BitVec.ofNat 32 ((if b0 then 1 else 0) + (if b1 then 2 else 0) +
    (if b2 then 4 else 0) + (if b3 then 8 else 0))

theorem packedFlags_bound : ∀ b0 b1 b2 b3,
    (packedFlags b0 b1 b2 b3).toNat < 16 := by decide

theorem moveMask_flags : ∀ b0 b1 b2 b3,
    moveMask64 (pack256 (mask64 b0) (mask64 b1) (mask64 b2) (mask64 b3)) =
      packedFlags b0 b1 b2 b3 := by decide

theorem lookup_flags : ∀ b0 b1 b2 b3,
    cascadeVector (packedFlags b0 b1 b2 b3) =
      pack256 (if b0 then 1 else 0) (if b1 then 1 else 0)
        (if b2 then 1 else 0) (if b3 then 1 else 0) := by decide

theorem packedFlags_disjoint : ∀ g0 g1 g2 g3 p0 p1 p2 p3,
    (¬ (g0 && p0) = true) → (¬ (g1 && p1) = true) →
    (¬ (g2 && p2) = true) → (¬ (g3 && p3) = true) →
    packedFlags g0 g1 g2 g3 &&& packedFlags p0 p1 p2 p3 = 0 := by decide

theorem incoming_flags : ∀ g0 g1 g2 g3 p0 p1 p2 p3,
    incomingMask (packedFlags g0 g1 g2 g3) (packedFlags p0 p1 p2 p3) =
      packedFlags false g0 (g1 || (p1 && g0))
        (g2 || (p2 && (g1 || (p1 && g0)))) := by decide

/-- Connects the actual packed-index arithmetic to the four lane increments. -/
theorem cascade_flags (g0 g1 g2 g3 p0 p1 p2 p3 : Bool)
    (h0 : ¬ (g0 && p0) = true) (h1 : ¬ (g1 && p1) = true)
    (h2 : ¬ (g2 && p2) = true) (h3 : ¬ (g3 && p3) = true) :
    cascadeVector (cascadeIndex (packedFlags g0 g1 g2 g3) (packedFlags p0 p1 p2 p3)) =
      pack256 0 (if g0 then 1 else 0) (if g1 || (p1 && g0) then 1 else 0)
        (if g2 || (p2 && (g1 || (p1 && g0))) then 1 else 0) := by
  let g := packedFlags g0 g1 g2 g3
  let p := packedFlags p0 p1 p2 p3
  have hg := packedFlags_bound g0 g1 g2 g3
  have hp := packedFlags_bound p0 p1 p2 p3
  have hd := packedFlags_disjoint g0 g1 g2 g3 p0 p1 p2 p3 h0 h1 h2 h3
  have equation := (packed_cascade ⟨g.toNat, hg⟩ ⟨p.toNat, hp⟩
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hd)).1
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at equation
  rw [equation, incoming_flags, lookup_flags]
  rfl

end UInt256Proof.SIMD
