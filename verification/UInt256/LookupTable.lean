import CIL.VectorMemory
import CIL.SIMD.Vector
import UInt256.Arithmetic.Cascade

open CIL CIL.Vector

namespace UInt256Proof.SIMD

/-- Sequential reading avoids repeatedly indexing the original table during
    kernel reduction. It is used only to check the existing lookup predicate. -/
def readLookupBytes (bytes : List (BitVec 8)) : Nat → Option Nat
  | 0 => some 0
  | count + 1 => do
    let lo ← bytes.head?
    let hi ← readLookupBytes bytes.tail count
    return lo.toNat + 256 * hi

theorem readStaticBytes_sequential (bytes : List (BitVec 8)) (offset count : Nat) :
    readStaticBytes bytes offset count = readLookupBytes (bytes.drop offset) count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    simp only [readStaticBytes, readLookupBytes, List.head?_drop, List.tail_drop, ih]

def cascadeVector (index : W32) : V256 :=
  pack256 (if index.getLsbD 0 then 1 else 0)
    (if index.getLsbD 1 then 1 else 0)
    (if index.getLsbD 2 then 1 else 0)
    (if index.getLsbD 3 then 1 else 0)

/-- Required contents of the extracted table; this predicate does not supply bytes. -/
def LookupValid (bytes : List (BitVec 8)) : Prop :=
  ∀ index : Fin 16, readStaticBytes bytes (32 * index.val) 32 =
    some (cascadeVector (BitVec.ofNat 32 index.val)).toNat

theorem read_lookup (bytes : List (BitVec 8)) (valid : LookupValid bytes)
    (index : W32) (bound : index.toNat < 16) (m : Memory) :
    read256 m (.static bytes (32 * index.toNat)) = some (.v256 (cascadeVector index)) := by
  have h := valid ⟨index.toNat, bound⟩
  change readStaticBytes bytes (32 * index.toNat) 32 =
    some (cascadeVector (BitVec.ofNat 32 index.toNat)).toNat at h
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  simp only [read256, h, Option.bind_eq_bind, Option.bind_some, pure,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem read_cascade_lookup (bytes : List (BitVec 8)) (valid : LookupValid bytes)
    (generated propagate : W32) (m : Memory) :
    read256 m (.static bytes (32 * (cascadeIndex generated propagate).toNat)) =
      some (.v256 (cascadeVector (cascadeIndex generated propagate))) :=
  read_lookup bytes valid _ (cascade_index_bound generated propagate) m

end UInt256Proof.SIMD
