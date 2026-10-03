import UInt256.Methods.Shift.ValueOutputs

open CIL UInt256Model

namespace UInt256Proof.Shift

theorem zero_nat : (0 : BitVec 256).toNat = 0 := by
  change (BitVec.ofNat 256 0).toNat = 0
  rw [BitVec.toNat_ofNat, Nat.zero_mod]
theorem left_store_zero (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      (limbs 0 <<< n)
      ((limbs 1 <<< n) ||| ((limbs 0 >>> 1) >>> (63-n)))
      ((limbs 2 <<< n) ||| ((limbs 1 >>> 1) >>> (63-n)))
      ((limbs 3 <<< n) ||| ((limbs 2 >>> 1) >>> (63-n))) =
    writeBytes memory out ((value limbs) <<< (n)).toNat 32 := by
  rw [← write_pack, left_pack_zero limbs n bound]

theorem left_store_one (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      0
      (limbs 0 <<< n)
      ((limbs 1 <<< n) ||| ((limbs 0 >>> 1) >>> (63-n)))
      ((limbs 2 <<< n) ||| ((limbs 1 >>> 1) >>> (63-n))) =
    writeBytes memory out ((value limbs) <<< (64+n)).toNat 32 := by
  rw [← write_pack, left_pack_one limbs n bound]

theorem left_store_two (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      0
      0
      (limbs 0 <<< n)
      ((limbs 1 <<< n) ||| ((limbs 0 >>> 1) >>> (63-n))) =
    writeBytes memory out ((value limbs) <<< (128+n)).toNat 32 := by
  rw [← write_pack, left_pack_two limbs n bound]

theorem left_store_three (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      0
      0
      0
      (limbs 0 <<< n) =
    writeBytes memory out ((value limbs) <<< (192+n)).toNat 32 := by
  rw [← write_pack, left_pack_three limbs n bound]

theorem right_store_zero (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      ((limbs 0 >>> n) ||| ((limbs 1 <<< 1) <<< (63-n)))
      ((limbs 1 >>> n) ||| ((limbs 2 <<< 1) <<< (63-n)))
      ((limbs 2 >>> n) ||| ((limbs 3 <<< 1) <<< (63-n)))
      (limbs 3 >>> n) =
    writeBytes memory out ((value limbs) >>> (n)).toNat 32 := by
  rw [← write_pack, right_pack_zero limbs n bound]

theorem right_store_one (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      ((limbs 1 >>> n) ||| ((limbs 2 <<< 1) <<< (63-n)))
      ((limbs 2 >>> n) ||| ((limbs 3 <<< 1) <<< (63-n)))
      (limbs 3 >>> n)
      0 =
    writeBytes memory out ((value limbs) >>> (64+n)).toNat 32 := by
  rw [← write_pack, right_pack_one limbs n bound]

theorem right_store_two (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      ((limbs 2 >>> n) ||| ((limbs 3 <<< 1) <<< (63-n)))
      (limbs 3 >>> n)
      0
      0 =
    writeBytes memory out ((value limbs) >>> (128+n)).toNat 32 := by
  rw [← write_pack, right_pack_two limbs n bound]

theorem right_store_three (memory : Memory) (out : Nat) (limbs : Limbs) (n : Nat) (bound : n < 64) :
    store4 memory out
      (limbs 3 >>> n)
      0
      0
      0 =
    writeBytes memory out ((value limbs) >>> (192+n)).toNat 32 := by
  rw [← write_pack, right_pack_three limbs n bound]

end UInt256Proof.Shift
