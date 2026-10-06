import CIL.Safety.ByteEncoding

namespace CIL.Safety

theorem byteNumber_lt (bytes : List (BitVec 8)) : byteNumber bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => decide
  | cons head tail ih =>
    have bound := head.isLt
    simp only [byteNumber, List.foldr_cons, List.length_cons, Nat.pow_succ]
    change head.toNat + 256 * byteNumber tail < 256 ^ tail.length * 256
    omega

theorem numberBytes_byteNumber (bytes : List (BitVec 8)) :
    numberBytes (byteNumber bytes) bytes.length = bytes := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
    rw [List.length_cons, numberBytes_succ]
    change BitVec.ofNat 8 (head.toNat + 256 * byteNumber tail) ::
      numberBytes ((head.toNat + 256 * byteNumber tail) / 256) tail.length = head :: tail
    have bound := head.isLt
    have quotient : (head.toNat + 256 * byteNumber tail) / 256 = byteNumber tail := by omega
    rw [quotient, ih]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    change (head.toNat + 256 * byteNumber tail) % 256 = head.toNat
    omega

#print axioms byteNumber_lt
#print axioms numberBytes_byteNumber
end CIL.Safety
