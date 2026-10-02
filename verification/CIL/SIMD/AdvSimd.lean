import CIL.SIMD.Vector

namespace CIL.Vector

/-- ARM EXT regards the first operand as the low half of the concatenation. -/
def advExtract64 (low high : V128) (index : Nat) : V128 :=
  (high ++ low).extractLsb' (64 * index) 128
end CIL.Vector
