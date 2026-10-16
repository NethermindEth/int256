import UInt256.Methods.Multiply.SoftwareProduct
open CIL
namespace UInt256Proof.Multiply

def digitLow (word : W64) : W64 := (word.setWidth 32).zeroExtend 64
def digitHigh (word : W64) : W64 := ((word >>> 32).setWidth 32).zeroExtend 64

theorem digitLow_nat (word : W64) : (digitLow word).toNat = word.toNat % 2^32 := by
  simp only [digitLow, BitVec.zeroExtend, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem digitHigh_nat (word : W64) : (digitHigh word).toNat = word.toNat / 2^32 := by
  have bound : word.toNat / 2^32 < 2^32 := by have h := word.isLt; omega
  simp only [digitHigh, BitVec.zeroExtend, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]

theorem digitLow_bound (word : W64) : (digitLow word).toNat < 2^32 := by
  rw [digitLow_nat]
  exact Nat.mod_lt _ (by decide)

theorem digitHigh_bound (word : W64) : (digitHigh word).toNat < 2^32 := by
  rw [digitHigh_nat]
  have h := word.isLt
  omega


theorem narrow_product_nat (a b : W64)
    (ha : a.toNat < 2^32) (hb : b.toNat < 2^32) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (word32_product_bound _ _ ha hb) (by decide))

def softwareLower (left right : W64) : W64 := digitLow left * digitLow right
def softwareMiddle (left right : W64) : W64 :=
  digitHigh left * digitLow right + (softwareLower left right >>> 32)
def softwareUpper (left right : W64) : W64 :=
  digitLow left * digitHigh right + digitLow (softwareMiddle left right)

def softwareLow (left right : W64) : W64 :=
  (softwareUpper left right <<< 32) ||| digitLow (softwareLower left right)
def softwareHigh (left right : W64) : W64 :=
  digitHigh left * digitHigh right + (softwareMiddle left right >>> 32) + (softwareUpper left right >>> 32)

theorem softwareLower_nat (a b : W64) :
    (softwareLower a b).toNat = (a.toNat % 2^32) * (b.toNat % 2^32) := by
  rw [softwareLower, narrow_product_nat _ _ (digitLow_bound a) (digitLow_bound b),
    digitLow_nat, digitLow_nat]

theorem softwareMiddle_nat (a b : W64) :
    (softwareMiddle a b).toNat = (a.toNat / 2^32) * (b.toNat % 2^32) +
      ((a.toNat % 2^32) * (b.toNat % 2^32)) / 2^32 := by
  rw [softwareMiddle, BitVec.toNat_add,
    narrow_product_nat _ _ (digitHigh_bound a) (digitLow_bound b),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, softwareLower_nat,
    digitHigh_nat, digitLow_nat]
  exact Nat.mod_eq_of_lt (software_middle_bound _ _ _
    (by have h := digitLow_bound a; simpa only [digitLow_nat] using h)
    (by have h := digitHigh_bound a; simpa only [digitHigh_nat] using h)
    (by have h := digitLow_bound b; simpa only [digitLow_nat] using h))

theorem softwareUpper_nat (a b : W64) :
    (softwareUpper a b).toNat = (a.toNat % 2^32) * (b.toNat / 2^32) +
      ((a.toNat / 2^32) * (b.toNat % 2^32) +
        ((a.toNat % 2^32) * (b.toNat % 2^32)) / 2^32) % 2^32 := by
  rw [softwareUpper, BitVec.toNat_add,
    narrow_product_nat _ _ (digitLow_bound a) (digitHigh_bound b),
    digitLow_nat, digitHigh_nat, digitLow_nat, softwareMiddle_nat]
  exact Nat.mod_eq_of_lt (software_upper_bound _ _ _ _
    (by have h := digitLow_bound a; simpa only [digitLow_nat] using h)
    (by have h := digitHigh_bound b; simpa only [digitHigh_nat] using h))

theorem shift32_nat (word : W64) :
    (word <<< 32).toNat = 2^32 * (word.toNat % 2^32) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm word.toNat (2^32),
    show 2^64 = 2^32 * 2^32 from rfl, Nat.mul_mod_mul_left]

theorem softwareLow_nat (a b : W64) :
    (softwareLow a b).toNat =
      2^32 * ((softwareUpper a b).toNat % 2^32) + (softwareLower a b).toNat % 2^32 := by
  rw [softwareLow, BitVec.toNat_or, shift32_nat, digitLow_nat]
  exact (Nat.two_pow_add_eq_or_of_lt
    (Nat.mod_lt (softwareLower a b).toNat (show 0 < 2^32 from by decide)) _).symm

theorem softwareHigh_nat (a b : W64) :
    (softwareHigh a b).toNat = (a.toNat / 2^32) * (b.toNat / 2^32) +
      (softwareMiddle a b).toNat / 2^32 + (softwareUpper a b).toNat / 2^32 := by
  have ha : a.toNat / 2^32 < 2^32 := by simpa only [digitHigh_nat] using digitHigh_bound a
  have hb : b.toNat / 2^32 < 2^32 := by simpa only [digitHigh_nat] using digitHigh_bound b
  have product := word32_product_bound _ _ ha hb
  have middle := (softwareMiddle a b).isLt
  have upper := (softwareUpper a b).isLt
  have first : (a.toNat / 2^32) * (b.toNat / 2^32) +
      (softwareMiddle a b).toNat / 2^32 < 2^64 := by omega
  have total : (a.toNat / 2^32) * (b.toNat / 2^32) +
      (softwareMiddle a b).toNat / 2^32 + (softwareUpper a b).toNat / 2^32 < 2^64 := by omega
  rw [softwareHigh, BitVec.toNat_add, BitVec.toNat_add,
    narrow_product_nat _ _ (digitHigh_bound a) (digitHigh_bound b),
    digitHigh_nat, digitHigh_nat, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt total]

theorem software_decomposition (a b : W64) :
    (softwareLow a b).toNat + 2^64 * (softwareHigh a b).toNat = a.toNat * b.toNat := by
  have arithmetic := software_product (a.toNat % 2^32) (a.toNat / 2^32)
    (b.toNat % 2^32) (b.toNat / 2^32)
  dsimp only at arithmetic
  rw [Nat.mod_add_div a.toNat (2^32), Nat.mod_add_div b.toNat (2^32)] at arithmetic
  rw [softwareLow_nat, softwareHigh_nat, softwareLower_nat, softwareMiddle_nat, softwareUpper_nat]
  omega

theorem softwareLow_correct (a b : W64) : softwareLow a b = lowProduct a b := by
  apply BitVec.eq_of_toNat_eq
  have arithmetic := software_decomposition a b
  have bound := (softwareLow a b).isLt
  simp only [lowProduct, BitVec.toNat_mul]
  omega

theorem softwareHigh_correct (a b : W64) : softwareHigh a b = highProduct a b := by
  apply BitVec.eq_of_toNat_eq
  rw [highProduct_nat]
  have arithmetic := software_decomposition a b
  have bound := (softwareLow a b).isLt
  omega

end UInt256Proof.Multiply

#print axioms UInt256Proof.Multiply.softwareLow_correct
#print axioms UInt256Proof.Multiply.softwareHigh_correct
