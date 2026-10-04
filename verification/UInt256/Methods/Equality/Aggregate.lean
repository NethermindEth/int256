import CIL.AggregateMemory
import CIL.MemoryLemmas
import UInt256.RepresentationLemmas
import UInt256.Methods.Bitwise.Aggregate
import CIL.VectorMemoryLemmas

open CIL UInt256Model
namespace UInt256Proof.Equality

theorem unsafeAdd_home_one (size frame kind index offset : Nat) (within : offset + size ≤ 32) :
    unsafeAdd size 1 (.home frame kind index offset) =
      some (.home frame kind index (offset + size)) := by
  simp [unsafeAdd,←Int.natCast_add]
  omega

@[simp] theorem readHomeBytes_write_local (m : Memory)
    (localFrame localIndex frame kind index offset count : Nat) (v : Value) :
    readHomeBytes (write m (.local localFrame localIndex) v) frame kind index offset count =
      readHomeBytes m frame kind index offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih => simp [readHomeBytes,write,ih]

@[simp] theorem read64_write_local_home (m : Memory)
    (localFrame localIndex frame kind index offset : Nat) (v : Value) :
    read64 (write m (.local localFrame localIndex) v) (.home frame kind index offset) =
      read64 m (.home frame kind index offset) := by
  simp only [read64,readHomeBytes_write_local]

@[simp] theorem read128_write_local_home (m : Memory)
    (localFrame localIndex frame kind index offset : Nat) (v : Value) :
    read128 (write m (.local localFrame localIndex) v) (.home frame kind index offset) =
      read128 m (.home frame kind index offset) := by
  simp only [read128,readHomeBytes_write_local]

@[simp] theorem read256_write_local_home (m : Memory)
    (localFrame localIndex frame kind index offset : Nat) (v : Value) :
    read256 (write m (.local localFrame localIndex) v) (.home frame kind index offset) =
      read256 m (.home frame kind index offset) := by
  simp only [read256,readHomeBytes_write_local]

@[simp] theorem read256_snapshot (m : Memory) (frame kind index : Nat) (bits : BitVec 256) :
    read256 (writeAggregate m frame kind index bits) (.home frame kind index 0) =
      some (.v256 bits) := by
  simpa only [read256, readAggregate, Nat.zero_add, Nat.le_refl, ite_true] using
    aggregate_snapshot_after_write m frame kind index bits

@[simp] theorem read256_writeAggregate_caller (m : Memory)
    (frame kind index base : Nat) (bits : BitVec 256) :
    read256 (writeAggregate m frame kind index bits) (.byte base) = read256 m (.byte base) :=
  read256_congr _ _ (writeHomeBytes_caller m frame kind index 0 bits.toNat 32) base

@[simp] theorem read256_clearHome_caller (m : Memory) (frame kind index base : Nat) :
    read256 (clearHome m frame kind index) (.byte base) = read256 m (.byte base) :=
  read256_congr _ _ (clearHome_caller m frame kind index) base

@[simp] theorem read128_writeAggregate_caller (m : Memory)
    (frame kind index base : Nat) (bits : BitVec 256) :
    read128 (writeAggregate m frame kind index bits) (.byte base) = read128 m (.byte base) :=
  read128_congr _ _ (writeHomeBytes_caller m frame kind index 0 bits.toNat 32) base

@[simp] theorem read128_clearHome_caller (m : Memory) (frame kind index base : Nat) :
    read128 (clearHome m frame kind index) (.byte base) = read128 m (.byte base) :=
  read128_congr _ _ (clearHome_caller m frame kind index) base

theorem writeHomeBytes_mod (m : Memory) (frame kind index offset number count : Nat) :
    writeHomeBytes m frame kind index offset (number % 256^count) count =
      writeHomeBytes m frame kind index offset number count := by
  induction count generalizing m offset number with
  | zero => rfl
  | succ count ih =>
    have low : BitVec.ofNat 8 (number % 256^(count+1)) = BitVec.ofNat 8 number := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.pow_succ]
      exact Nat.mod_mul_left_mod number (256^count) 256
    simp only [CIL.writeHomeBytes]
    rw [low]
    simp only [Nat.pow_succ, Nat.mod_mul_left_div_self]
    exact ih _ _ _

theorem readAggregate_wordWrites (m : Memory) (frame kind index : Nat) (word : W64) :
    readAggregate (writeHomeBytes (writeHomeBytes (writeHomeBytes (writeHomeBytes m
      frame kind index 0 word.toNat 8) frame kind index 8 0 8)
      frame kind index 16 0 8) frame kind index 24 0 8) frame kind index =
      some (.v256 (value (fun i => if i = 0 then word else BitVec.ofNat 64 0))) := by
  simpa only [BitVec.toNat_ofNat, Nat.zero_mod, ite_self] using
    Bitwise.aggregate_fourWrites m frame kind index word
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)

theorem readAggregate_numberWrites (m : Memory) (frame kind index number : Nat) :
    readAggregate (writeHomeBytes (writeHomeBytes (writeHomeBytes (writeHomeBytes m
      frame kind index 0 number 8) frame kind index 8 0 8)
      frame kind index 16 0 8) frame kind index 24 0 8) frame kind index =
      some (.v256 (value (fun i => if i = 0 then BitVec.ofNat 64 number else BitVec.ofNat 64 0))) := by
  have words := readAggregate_wordWrites m frame kind index (BitVec.ofNat 64 number)
  simpa only [BitVec.toNat_ofNat, show 2^64 = (256 : Nat)^8 from rfl, writeHomeBytes_mod] using words

@[simp] theorem read64_writeHomeBytes_caller (m : Memory)
    (frame kind index offset number count base : Nat) :
    read64 (writeHomeBytes m frame kind index offset number count) (.byte base) =
      read64 m (.byte base) :=
  read64_congr _ _ (writeHomeBytes_caller m frame kind index offset number count) base

@[simp] theorem read64_writeAggregate_caller (m : Memory)
    (frame kind index base : Nat) (bits : BitVec 256) :
    read64 (writeAggregate m frame kind index bits) (.byte base) = read64 m (.byte base) := by
  exact read64_writeHomeBytes_caller m frame kind index 0 bits.toNat 32 base

@[simp] theorem read64_clearHome_caller (m : Memory) (frame kind index base : Nat) :
    read64 (clearHome m frame kind index) (.byte base) = read64 m (.byte base) :=
  read64_congr _ _ (clearHome_caller m frame kind index) base

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

theorem read128_snapshot (m : Memory) (frame kind index : Nat) (bits : BitVec 256)
    (half : Fin 2) :
    read128 (writeAggregate m frame kind index bits) (.home frame kind index (16 * half.val)) =
      some (.v128 (bits.extractLsb' (128 * half.val) 128)) := by
  simp only [read128,writeAggregate]
  have within : 16 * half.val + 16 ≤ 32 := by omega
  have slice := readHomeBytes_slice m frame kind index 0 bits.toNat 32 (16 * half.val) 16 within
  simp only [Nat.zero_add] at slice
  rw [ite_eq_left within,slice]
  simp only [Option.bind_eq_bind,Option.pure_def,Option.bind_some]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  have powers : 256 ^ (16 * half.val) = 2 ^ (128 * half.val) := by
    rw [show (256 : Nat) = 2^8 from rfl,←Nat.pow_mul]
    congr 1
    omega
  rw [powers,show (256 : Nat)^16 = 2^128 from rfl,Nat.mod_mod]

theorem read128_snapshot0 (m : Memory) (frame kind index : Nat) (bits : BitVec 256) :
    read128 (writeAggregate m frame kind index bits) (.home frame kind index 0) =
      some (.v128 (bits.extractLsb' 0 128)) := read128_snapshot m frame kind index bits 0

theorem read128_snapshot1 (m : Memory) (frame kind index : Nat) (bits : BitVec 256) :
    read128 (writeAggregate m frame kind index bits) (.home frame kind index 16) =
      some (.v128 (bits.extractLsb' 128 128)) := read128_snapshot m frame kind index bits 1

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

/-- Updating three high words preserves the snapshot's low word. -/
theorem readAggregate_highWordWrites (m : Memory) (frame kind index : Nat)
    (bits : BitVec 256) (r1 r2 r3 : W64) :
    readAggregate (writeHomeBytes (writeHomeBytes (writeHomeBytes
      (writeHomeBytes m frame kind index 0 bits.toNat 32)
      frame kind index 8 r1.toNat 8) frame kind index 16 r2.toNat 8)
      frame kind index 24 r3.toNat 8) frame kind index =
      some (.v256 (value (fun i => if i=0 then decode bits 0 else
        if i=1 then r1 else if i=2 then r2 else r3))) := by
  have low : readHomeBytes (writeHomeBytes m frame kind index 0 bits.toNat 32)
      frame kind index 0 8 = some (bits.toNat % 256^8) := by
    simpa only [Nat.zero_add,Nat.pow_zero,Nat.div_one] using
      readHomeBytes_slice m frame kind index 0 bits.toNat 32 0 8 (by decide)
  unfold readAggregate
  rw [show 32 = 8 + 24 from rfl,readHomeBytes_append]
  rw [show 24 = 8 + 16 from rfl,readHomeBytes_append]
  rw [show 16 = 8 + 8 from rfl,readHomeBytes_append]
  simp only [Nat.reduceAdd]
  simp [readHomeBytes_write_disjoint,readHomeBytes_after_write,
    low, Nat.mod_eq_of_lt r1.isLt,Nat.mod_eq_of_lt r2.isLt,
    Nat.mod_eq_of_lt r3.isLt]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,UInt256Proof.value_toNat,decode,Fin.val_zero]
  simp
  omega

end UInt256Proof.Equality
