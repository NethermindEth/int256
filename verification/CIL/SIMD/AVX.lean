import CIL.SIMD.Vector

namespace CIL.Vector

def moveMask64 (x : V256) : W32 :=
  (List.range 4).foldl (fun acc i =>
    acc ||| (BitVec.ofNat 32 (if (lane64 x i).msb then 1 else 0) <<< i)) 0

def moveMask32 (x : V256) : W32 :=
  (List.range 8).foldl (fun acc i =>
    acc ||| (BitVec.ofNat 32 (if (lane32 x i).msb then 1 else 0) <<< i)) 0

end CIL.Vector
