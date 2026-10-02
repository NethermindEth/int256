import CIL.SIMD.Vector

namespace CIL.Vector

def bextr32 (x : W32) (start length : Nat) : W32 :=
  if start ≥ 32 then 0 else
    (x >>> start) &&& (BitVec.ofNat 32 (2 ^ (min length (32 - start)) - 1))

end CIL.Vector
