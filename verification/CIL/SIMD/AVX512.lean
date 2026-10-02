import CIL.SIMD.Vector

namespace CIL.Vector

/-- VALIGNQ's immediate is masked to the lane-count minus one. -/
def alignRight64 (high low : V256) (count : Nat) : V256 :=
  (high ++ low).extractLsb' (64 * (count % 4)) 256

/-- Intel truth-table index is 4*a + 2*b + c at each bit position. -/
def ternaryLogic (a b c : BitVec n) (control : BitVec 8) : BitVec n :=
  (List.range 8).foldl (fun acc i =>
    if control.getLsbD i then
      acc ||| ((if i.testBit 2 then a else ~~~a) &&&
        (if i.testBit 1 then b else ~~~b) &&& (if i.testBit 0 then c else ~~~c))
    else acc) 0

end CIL.Vector
