import CIL.SIMD.Vector

open CIL

namespace UInt256Proof.SIMD

/-- The packed carry/borrow computation used by both production AVX routes. -/
def cascadeIndex (generated propagate : W32) : W32 :=
  (propagate ^^^ (propagate + 2 * generated)) &&& 15

def incoming2 (generated propagate : W32) : Bool :=
  generated.getLsbD 1 || (propagate.getLsbD 1 && generated.getLsbD 0)

def incoming3 (generated propagate : W32) : Bool :=
  generated.getLsbD 2 || (propagate.getLsbD 2 && incoming2 generated propagate)

def finalCarry (generated propagate : W32) : Bool :=
  generated.getLsbD 3 || (propagate.getLsbD 3 && incoming3 generated propagate)

def incomingMask (generated propagate : W32) : W32 :=
  BitVec.ofNat 32 ((if generated.getLsbD 0 then 2 else 0) +
    (if incoming2 generated propagate then 4 else 0) +
    (if incoming3 generated propagate then 8 else 0))

/-- Exhaustive finite arithmetic, checked by the kernel, rather than a native solver.
    A lane cannot both generate and propagate a carry (or borrow). -/
theorem packed_cascade : ∀ (g p : Fin 16),
    ((BitVec.ofNat 32 g.val) &&& (BitVec.ofNat 32 p.val)) = 0 →
    cascadeIndex (BitVec.ofNat 32 g.val) (BitVec.ofNat 32 p.val) =
      incomingMask (BitVec.ofNat 32 g.val) (BitVec.ofNat 32 p.val) ∧
    ((BitVec.ofNat 32 p.val + 2 * BitVec.ofNat 32 g.val).getLsbD 4 =
      finalCarry (BitVec.ofNat 32 g.val) (BitVec.ofNat 32 p.val)) := by decide

theorem cascade_index_bound (generated propagate : W32) :
    (cascadeIndex generated propagate).toNat < 16 := by
  unfold cascadeIndex
  rw [BitVec.toNat_and]
  exact Nat.and_lt_two_pow _ (by decide : (15 : W32).toNat < 2^4)

/-- The actual CIL int32-to-native conversion preserves the masked lookup index. -/
theorem cascade_native_offset (generated propagate : W32) :
    ((propagate.toNat % 18446744073709551616 ^^^
      (propagate.toNat + 2 * generated.toNat) % 4294967296 % 18446744073709551616) &&& 15) =
      ((propagate ^^^ (propagate + BitVec.ofNat 32 2 * generated)) &&&
        BitVec.ofNat 32 15).toNat := by
  have hp : propagate.toNat < 2^64 := by have h := propagate.isLt; omega
  have hm : (propagate.toNat + 2 * generated.toNat) % 2^32 < 2^64 := by
    have h := Nat.mod_lt (propagate.toNat + 2 * generated.toNat) (by decide : 0 < 2^32)
    omega
  simp only [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hm]
  rw [Nat.add_mod_mod]

end UInt256Proof.SIMD
