import CIL.MemoryLemmas
import UInt256.Representation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem read_initial (m : Bytes) (base n : Nat) :
    readBytes (byteMemory m) base n = some (byteNumber m base n) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp [readBytes, byteMemory, byteNumber, ih]

theorem byteNumber_bound (m : Bytes) (base n : Nat) : byteNumber m base n < 256^n := by
  induction n generalizing base with
  | zero => simp [byteNumber]
  | succ n ih =>
    have hb := (m base).isLt
    have hi := ih (base + 1)
    simp only [byteNumber, Nat.pow_succ]
    omega

theorem byteNumber_append (m : Bytes) (base low high : Nat) :
    byteNumber m base (low + high) = byteNumber m base low +
      256^low * byteNumber m (base + low) high := by
  induction low generalizing base with
  | zero => simp [byteNumber]
  | succ low ih =>
    simp only [Nat.succ_add, byteNumber, ih, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    ac_rfl

def inputLimbs (m : Bytes) (base : Nat) : Limbs :=
  fun i => BitVec.ofNat 64 (byteNumber m (base + 8 * i.val) 8)

theorem input_limb_nat (m : Bytes) (base : Nat) (i : Fin 4) :
    (inputLimbs m base i).toNat = byteNumber m (base + 8 * i.val) 8 := by
  have bound := byteNumber_bound m (base + 8 * i.val) 8
  change byteNumber m (base + 8 * i.val) 8 < 2^64 at bound
  exact Nat.mod_eq_of_lt bound

-- Normalize the four input loads once for the execution proofs.
theorem limb_reads (m : Memory) (base : Nat) (a : Limbs)
    (h : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i))) :
    read64 m (.byte base) = some (.i64 (a 0)) ∧
    read64 m (.byte (base + 8)) = some (.i64 (a 1)) ∧
    read64 m (.byte (base + 16)) = some (.i64 (a 2)) ∧
    read64 m (.byte (base + 24)) = some (.i64 (a 3)) :=
  ⟨h 0, h 1, h 2, h 3⟩

theorem read64_initial (m : Bytes) (base : Nat) (i : Fin 4) :
    read64 (byteMemory m) (.byte (base + 8 * i.val)) = some (.i64 (inputLimbs m base i)) := by
  simp [read64, read_initial, inputLimbs]

theorem input_value (m : Bytes) (base : Nat) : value (inputLimbs m base) = byteValue m base := by
  have h0 := byteNumber_append m base 8 24
  have h1 := byteNumber_append m (base + 8) 8 16
  have h2 := byteNumber_append m (base + 16) 8 8
  have off1 : base + 8 + 8 = base + 16 := by omega
  have off2 : base + 16 + 8 = base + 24 := by omega
  rw [off1] at h1
  rw [off2] at h2
  have pow8 : (256 : Nat)^8 = 2^64 := by decide
  simp only [pow8, show 8 + 24 = 32 from rfl, show 8 + 16 = 24 from rfl,
    show 8 + 8 = 16 from rfl] at h0 h1 h2
  have total : byteNumber m base 32 = byteNumber m base 8 +
      byteNumber m (base + 8) 8 * 2^64 + byteNumber m (base + 16) 8 * 2^128 +
      byteNumber m (base + 24) 8 * 2^192 := by
    rw [h0, h1, h2]
    simp only [Nat.mul_add, ← Nat.mul_assoc]
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [value, byteValue, input_limb_nat]
  simp only [BitVec.toNat_ofNat,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero,
    show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl]
  exact congrArg (fun n => n % 2^256) total.symm
theorem decode_value (a : Limbs) : decode (value a) = a := by
  funext i
  rcases i with ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have h0 := (a 0).isLt
  have h1 := (a 1).isLt
  have h2 := (a 2).isLt
  have h3 := (a 3).isLt
  rcases cases with h | h | h | h
  all_goals
    subst i
    apply BitVec.eq_of_toNat_eq
    simp [decode, value]
    omega

theorem representation_injective (a b : Limbs) (h : value a = value b) : a = b := by
  rw [← decode_value a, ← decode_value b, h]

theorem value_decode (v : BitVec 256) : value (decode v) = v := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp [value, decode]
  change (v.toNat % 2^64 + (v.toNat / 2^64 % 2^64) * 2^64 +
    (v.toNat / 2^128 % 2^64) * 2^128 +
    (v.toNat / 2^192 % 2^64) * 2^192) % 2^256 = v.toNat
  have hdiv1 : v.toNat / 2^64 / 2^64 = v.toNat / 2^128 := by
    rw [Nat.div_div_eq_div_mul]
  have hdiv2 : v.toNat / 2^128 / 2^64 = v.toNat / 2^192 := by
    rw [Nat.div_div_eq_div_mul]
  omega

end UInt256Proof
