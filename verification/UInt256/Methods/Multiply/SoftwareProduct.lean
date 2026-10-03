import UInt256.Methods.Multiply.Product
namespace UInt256Proof.Multiply

/-- The software widening multiply carries the two middle 32-bit products
    separately. This identity is independent of the extracted instruction order. -/
theorem software_product (al ah bl bh : Nat) :
    let low := al * bl
    let middle := ah * bl + low / 2^32
    let upper := al * bh + middle % 2^32
    low % 2^32 + 2^32 * (upper % 2^32) +
      2^64 * (ah * bh + middle / 2^32 + upper / 2^32) =
    (al + 2^32 * ah) * (bl + 2^32 * bh) := by
  dsimp only
  have lo := Nat.mod_add_div (al * bl) (2^32)
  have mid := Nat.mod_add_div (ah * bl + al * bl / 2^32) (2^32)
  have top := Nat.mod_add_div (al * bh + (ah * bl + al * bl / 2^32) % 2^32) (2^32)
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  rw [Nat.mul_left_comm al (2^32) bh, Nat.mul_left_comm ah (2^32) bh]
  omega
theorem word32_product_bound (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    a * b ≤ (2^32 - 1) * (2^32 - 1) := by
  exact Nat.mul_le_mul (by omega) (by omega)

theorem software_middle_bound (al ah bl : Nat)
    (hal : al < 2^32) (hah : ah < 2^32) (hbl : bl < 2^32) :
    ah * bl + al * bl / 2^32 < 2^64 := by
  have lower := word32_product_bound al bl hal hbl
  have upper := word32_product_bound ah bl hah hbl
  omega

theorem software_upper_bound (al ah bl bh : Nat)
    (hal : al < 2^32) (hbh : bh < 2^32) :
    al * bh + (ah * bl + al * bl / 2^32) % 2^32 < 2^64 := by
  have product := word32_product_bound al bh hal hbh
  have remainder := Nat.mod_lt (ah * bl + al * bl / 2^32) (show 0 < 2^32 by decide)
  omega

end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.software_product
