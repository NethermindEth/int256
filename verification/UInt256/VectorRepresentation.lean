import CIL.VectorMemoryLemmas
import UInt256.StorageLemmas
import CIL.SIMD.Vector

open CIL UInt256Model

namespace UInt256Model

def halfValue (m : Bytes) (base : Nat) : BitVec 128 :=
  BitVec.ofNat 128 (byteNumber m base 16)

end UInt256Model

namespace UInt256Proof

theorem pack128_number (lo hi : W64) :
    (CIL.Vector.pack128 lo hi).toNat = lo.toNat + 2^64 * hi.toNat := by
  simp only [CIL.Vector.pack128, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
  omega

theorem write128_two_limbs (m : Memory) (base : Nat) (lo hi : W64) :
    writeBytes m base (CIL.Vector.pack128 lo hi).toNat 16 =
      writeBytes (writeBytes m base lo.toNat 8) (base + 8) hi.toNat 8 := by
  rw [pack128_number]
  rw [show 16 = 8 + 8 from rfl, writeBytes_append]
  have divided : (lo.toNat + 2^64 * hi.toNat) / 256^8 = hi.toNat := by
    have hl := lo.isLt
    omega
  rw [divided]
  congr 1
  rw [← writeBytes_mod m base (lo.toNat + 2^64 * hi.toNat) 8]
  have reduced : (lo.toNat + 2^64 * hi.toNat) % 256^8 = lo.toNat := by
    have hl := lo.isLt
    omega
  rw [reduced]

theorem read128_of_limbs (m : Memory) (base : Nat) (lo hi : W64)
    (hl : read64 m (.byte base) = some (.i64 lo))
    (hh : read64 m (.byte (base + 8)) = some (.i64 hi)) :
    read128 m (.byte base) = some (.v128 (CIL.Vector.pack128 lo hi)) := by
  have joined := readBytes_append_of m base 8 8 lo.toNat hi.toNat
    (readBytes_of_read64 m base lo hl) (readBytes_of_read64 m (base + 8) hi hh)
  simp only [show 8 + 8 = 16 from rfl] at joined
  simp only [read128, joined]
  change some (Value.v128 (BitVec.ofNat 128 (lo.toNat + 256^8 * hi.toNat))) =
    some (Value.v128 (CIL.Vector.pack128 lo hi))
  congr 2
  apply BitVec.eq_of_toNat_eq
  have hlo := lo.isLt
  have hhi := hi.isLt
  simp only [BitVec.toNat_ofNat, CIL.Vector.pack128, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlo, Nat.shiftLeft_eq]
  omega

theorem read128_initial (m : Bytes) (base : Nat) :
    read128 (byteMemory m) (.byte base) = some (.v128 (halfValue m base)) := by
  simp [read128, read_initial, halfValue]

theorem pack256_number (a b c d : W64) :
    (CIL.Vector.pack256 a b c d).toNat =
      (a.toNat + 2^64 * b.toNat) + 2^128 * (c.toNat + 2^64 * d.toNat) := by
  change ((CIL.Vector.pack128 c d) ++ (CIL.Vector.pack128 a b)).toNat = _
  rw [BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (CIL.Vector.pack128 a b).isLt,
    Nat.shiftLeft_eq, pack128_number, pack128_number]
  omega

theorem read256_of_limbs (m : Memory) (base : Nat) (a b c d : W64)
    (ha : read64 m (.byte base) = some (.i64 a))
    (hb : read64 m (.byte (base + 8)) = some (.i64 b))
    (hc : read64 m (.byte (base + 16)) = some (.i64 c))
    (hd : read64 m (.byte (base + 24)) = some (.i64 d)) :
    read256 m (.byte base) = some (.v256 (CIL.Vector.pack256 a b c d)) := by
  have low := readBytes_append_of m base 8 8 a.toNat b.toNat
    (readBytes_of_read64 m base a ha) (readBytes_of_read64 m (base + 8) b hb)
  have high := readBytes_append_of m (base + 16) 8 8 c.toNat d.toNat
    (readBytes_of_read64 m (base + 16) c hc)
    (readBytes_of_read64 m (base + 24) d hd)
  have joined := readBytes_append_of m base 16 16 _ _ low high
  simp only [read256, joined]
  change some (Value.v256 (BitVec.ofNat 256
    ((a.toNat + 2^64 * b.toNat) + 2^128 * (c.toNat + 2^64 * d.toNat)))) =
    some (Value.v256 (CIL.Vector.pack256 a b c d))
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, pack256_number]
  have bound := (CIL.Vector.pack256 a b c d).isLt
  rw [pack256_number] at bound
  exact Nat.mod_eq_of_lt bound

theorem read256_initial (m : Bytes) (base : Nat) :
    read256 (byteMemory m) (.byte base) = some (.v256 (byteValue m base)) := by
  simp [read256, read_initial, byteValue]

theorem read256_initial_limbs (m : Bytes) (base : Nat) :
    read256 (byteMemory m) (.byte base) = some (.v256 (value (inputLimbs m base))) := by
  rw [input_value]
  exact read256_initial m base

/-- The adjacent unaligned 128-bit loads encode exactly the same initial
    four limbs as the full-width load. -/
theorem initial_halves (m : Bytes) (base : Nat) :
    BitVec.ofNat 256 ((halfValue m base).toNat +
      2^128 * (halfValue m (base + 16)).toNat) = byteValue m base := by
  have lo := byteNumber_bound m base 16
  have hi := byteNumber_bound m (base + 16) 16
  have halves := byteNumber_append m base 16 16
  change byteNumber m base 16 < 2^128 at lo
  change byteNumber m (base + 16) 16 < 2^128 at hi
  simp only [halfValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lo, Nat.mod_eq_of_lt hi,
    byteValue]
  apply congrArg (BitVec.ofNat 256)
  simpa only [show (256 : Nat)^16 = 2^128 from rfl,
    show 16 + 16 = 32 from rfl] using halves.symm

/-- A vector store is the existing four-limb store, with no assumptions
    about disjoint input/output ranges. -/
theorem vector_store4 (m : Memory) (base : Nat) (bits : BitVec 256) :
    write256 m (.byte base) bits =
      some (store4 m base (decode bits 0) (decode bits 1) (decode bits 2) (decode bits 3)) := by
  simp only [write256, store4_value]
  have lanes : (fun i : Fin 4 => if i.val = 0 then decode bits 0 else
      if i.val = 1 then decode bits 1 else if i.val = 2 then decode bits 2 else
        decode bits 3) = decode bits := by
    funext i
    rcases i with ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with h | h | h | h
    all_goals subst i; rfl
  rw [lanes, value_decode]

theorem write256_four_limbs (m : Memory) (base : Nat) (a b c d : W64) :
    write256 m (.byte base) (CIL.Vector.pack256 a b c d) =
      some (store4 m base a b c d) := by
  rw [store4_value]
  simp only [write256]
  congr 2
  rw [pack256_number]
  simp only [value, Fin.val_zero, Fin.val_one, Fin.val_two,
    show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]
  have bound := (CIL.Vector.pack256 a b c d).isLt
  rw [pack256_number] at bound
  rw [Nat.mul_add] at bound ⊢
  omega

theorem writeBytes_four_limbs (m : Memory) (base : Nat) (a b c d : W64) :
    writeBytes m base (CIL.Vector.pack256 a b c d).toNat 32 = store4 m base a b c d :=
  Option.some.inj (write256_four_limbs m base a b c d)

theorem store4_overwrite_same (m : Memory) (base : Nat) (a b c d x y z w : W64) :
    store4 (store4 m base a b c d) base x y z w = store4 m base x y z w := by
  simp only [store4_value, writeBytes_overwrite_same]

end UInt256Proof
