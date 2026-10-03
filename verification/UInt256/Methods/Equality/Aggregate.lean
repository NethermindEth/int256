import CIL.AggregateMemory
import UInt256.RepresentationLemmas

open CIL UInt256Model
namespace UInt256Proof.Equality

theorem writeHomeBytes_append (m : Memory) (frame kind index offset number low high : Nat) :
    writeHomeBytes m frame kind index offset number (low + high) =
      writeHomeBytes (writeHomeBytes m frame kind index offset number low)
        frame kind index (offset + low) (number / 256^low) high := by
  induction low generalizing m offset number with
  | zero => simp [CIL.writeHomeBytes]
  | succ low ih =>
    simp only [Nat.succ_add,CIL.writeHomeBytes,ih,Nat.pow_succ,Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm 256 (256^low)]
    congr 1 <;> omega

theorem readHomeBytes_slice (m : Memory)
    (frame kind index offset number total skip count : Nat) (within : skip + count ≤ total) :
    readHomeBytes (writeHomeBytes m frame kind index offset number total)
      frame kind index (offset + skip) count =
        some (number / 256^skip % 256^count) := by
  have sizes : total = skip + (count + (total - skip - count)) := by omega
  rw [sizes,writeHomeBytes_append m frame kind index offset number skip,
    writeHomeBytes_append _ frame kind index (offset + skip) (number / 256^skip) count,
    readHomeBytes_write_disjoint _ frame kind index (offset + skip + count) _ _
      (offset + skip) count (Or.inl (by omega)),
    readHomeBytes_after_write]

theorem read64_snapshot (m : Memory) (frame kind index : Nat) (bits : BitVec 256)
    (limb : Fin 4) :
    read64 (writeAggregate m frame kind index bits) (.home frame kind index (8 * limb.val)) =
      some (.i64 (decode bits limb)) := by
  simp only [read64,writeAggregate]
  have within : 8 * limb.val + 8 ≤ 32 := by omega
  have slice := readHomeBytes_slice m frame kind index 0 bits.toNat 32 (8 * limb.val) 8 within
  simp only [Nat.zero_add] at slice
  rw [ite_eq_left within,slice]
  simp only [decode,Option.bind_eq_bind,Option.pure_def,Option.bind_some]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have powers : 256 ^ (8 * limb.val) = 2 ^ (64 * limb.val) := by
    rw [show (256 : Nat) = 2^8 from rfl,←Nat.pow_mul]
    congr 1
    omega
  rw [powers,show (256 : Nat)^8 = 2^64 from rfl,Nat.mod_mod]

theorem read64_snapshot0 (m : Memory) (frame kind index : Nat) (bits : BitVec 256) :
    read64 (writeAggregate m frame kind index bits) (.home frame kind index 0) =
      some (.i64 (decode bits 0)) := read64_snapshot m frame kind index bits 0

theorem read64_snapshot1 (m : Memory) (frame kind index : Nat) (bits : BitVec 256) :
    read64 (writeAggregate m frame kind index bits) (.home frame kind index 8) =
      some (.i64 (decode bits 1)) := read64_snapshot m frame kind index bits 1

theorem read64_snapshot2 (m : Memory) (frame kind index : Nat) (bits : BitVec 256) :
    read64 (writeAggregate m frame kind index bits) (.home frame kind index 16) =
      some (.i64 (decode bits 2)) := read64_snapshot m frame kind index bits 2

theorem read64_snapshot3 (m : Memory) (frame kind index : Nat) (bits : BitVec 256) :
    read64 (writeAggregate m frame kind index bits) (.home frame kind index 24) =
      some (.i64 (decode bits 3)) := read64_snapshot m frame kind index bits 3

end UInt256Proof.Equality
