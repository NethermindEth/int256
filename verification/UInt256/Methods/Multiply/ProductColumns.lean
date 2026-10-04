import UInt256.Methods.Multiply.Columns
import UInt256.Methods.Multiply.PartialProducts
open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

def firstColumn (a b : Limbs) : W64 × W64 :=
  column (highProduct (a 0) (b 0)) [lowProduct (a 0) (b 1), lowProduct (a 1) (b 0)]

def secondColumn (a b : Limbs) : W64 × W64 :=
  column (firstColumn a b).2 [highProduct (a 0) (b 1), highProduct (a 1) (b 0),
    lowProduct (a 0) (b 2), lowProduct (a 1) (b 1), lowProduct (a 2) (b 0)]

def topWords (a b : Limbs) : List W64 :=
  [lowProduct (a 0) (b 3), lowProduct (a 1) (b 2), lowProduct (a 2) (b 1),
    lowProduct (a 3) (b 0), highProduct (a 0) (b 2), highProduct (a 1) (b 1),
    highProduct (a 2) (b 0), (secondColumn a b).2]

def productLimbs (a b : Limbs) : Limbs := fun i =>
  if i.val = 0 then lowProduct (a 0) (b 0) else
  if i.val = 1 then (firstColumn a b).1 else
  if i.val = 2 then (secondColumn a b).1 else (topWords a b).sum

def productTotal (a b : Limbs) : Nat :=
  (lowProduct (a 0) (b 0)).toNat + (firstColumn a b).1.toNat * 2^64 +
    (secondColumn a b).1.toNat * 2^128 + (topWords a b).sum.toNat * 2^192

def productDiscarded (a b : Limbs) : Nat :=
  ((topWords a b).map BitVec.toNat).sum / 2^64 +
    (highProduct (a 0) (b 3)).toNat + (highProduct (a 1) (b 2)).toNat +
    (highProduct (a 2) (b 1)).toNat + (highProduct (a 3) (b 0)).toNat

theorem product_conservation (a b : Limbs) :
    productTotal a b + productDiscarded a b * 2^256 = retainedProducts a b := by
  have column1 := column_correct (highProduct (a 0) (b 0))
    [lowProduct (a 0) (b 1), lowProduct (a 1) (b 0)] (by change 2 < 2^64; decide)
  have column2 := column_correct (firstColumn a b).2
    [highProduct (a 0) (b 1), highProduct (a 1) (b 0),
      lowProduct (a 0) (b 2), lowProduct (a 1) (b 1), lowProduct (a 2) (b 0)] (by change 5 < 2^64; decide)
  change (firstColumn a b).1.toNat + 2^64 * (firstColumn a b).2.toNat = _ at column1
  change (secondColumn a b).1.toNat + 2^64 * (secondColumn a b).2.toNat = _ at column2
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at column1 column2
  have top := Nat.mod_add_div ((topWords a b).map BitVec.toNat).sum (2^64)
  rw [← sum_words_nat] at top
  simp only [topWords, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at top
  have p00 := product_decomposition (a 0) (b 0)
  have p01 := product_decomposition (a 0) (b 1)
  have p10 := product_decomposition (a 1) (b 0)
  have p02 := product_decomposition (a 0) (b 2)
  have p11 := product_decomposition (a 1) (b 1)
  have p20 := product_decomposition (a 2) (b 0)
  have p03 := product_decomposition (a 0) (b 3)
  have p12 := product_decomposition (a 1) (b 2)
  have p21 := product_decomposition (a 2) (b 1)
  have p30 := product_decomposition (a 3) (b 0)
  simp only [productTotal, productDiscarded, retainedProducts, topWords, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  omega
end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.product_conservation
