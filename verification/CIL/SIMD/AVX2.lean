import CIL.SIMD.Vector

namespace CIL.Vector

def permute4x64 (x : V256) (control : BitVec 8) : V256 :=
  pack256 (lane64 x ((control.extractLsb' 0 2).toNat))
    (lane64 x ((control.extractLsb' 2 2).toNat))
    (lane64 x ((control.extractLsb' 4 2).toNat))
    (lane64 x ((control.extractLsb' 6 2).toNat))

def blend32 (a b : V256) (control : BitVec 8) : V256 :=
  let lane := fun i => if control.getLsbD i then lane32 b i else lane32 a i
  ((lane 7 ++ lane 6) ++ (lane 5 ++ lane 4)) ++
    ((lane 3 ++ lane 2) ++ (lane 1 ++ lane 0))

end CIL.Vector
