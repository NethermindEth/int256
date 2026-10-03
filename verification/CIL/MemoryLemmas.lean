import CIL.Semantics

open CIL
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

@[simp] theorem writeBytes_home (m : Memory)
    (base word count frame kind index offset : Nat) :
    writeBytes m base word count (.home frame kind index offset) =
      m (.home frame kind index offset) := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih => rw [writeBytes, ih]; simp [write]

theorem readBytes_congr (m n : Memory)
    (h : ∀ address, m (.byte address) = n (.byte address)) (base count : Nat) :
    readBytes m base count = readBytes n base count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => simp [readBytes, h, ih]

theorem read64_congr (m n : Memory)
    (h : ∀ address, m (.byte address) = n (.byte address)) (base : Nat) :
    read64 m (.byte base) = read64 n (.byte base) := by
  simp only [read64, readBytes_congr m n h]

theorem read64_local (m : Memory) (frame index : Nat) :
    read64 m (.local frame index) = (m (.local frame index)).bind (fun value =>
      match value with
      | .i64 word => some (.i64 word)
      | _ => none) := by rfl

@[simp] theorem readBytes_write_local (m : Memory) (frame index base count : Nat) (v : Value) :
    readBytes (write m (.local frame index) v) base count = readBytes m base count := by
  apply readBytes_congr
  intro address
  simp [write]

theorem initLocals_bytes (m : Memory) (frame : Nat) (values : List Value) (address : Nat) :
    initLocals m frame values (.byte address) = m (.byte address) := by
  unfold initLocals
  generalize values.zipIdx = entries
  induction entries generalizing m with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [write]

@[simp] theorem readBytes_initLocals (m : Memory) (frame base count : Nat) (values : List Value) :
    readBytes (initLocals m frame values) base count = readBytes m base count := by
  apply readBytes_congr
  exact initLocals_bytes m frame values

theorem initLocals_other_frame (m : Memory) (frame other index : Nat) (values : List Value)
    (hn : other ≠ frame) :
    initLocals m frame values (.local other index) = m (.local other index) := by
  unfold initLocals
  generalize values.zipIdx = entries
  induction entries generalizing m with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [write, hn]
theorem writeBytes_outside (m : Memory) (base word n address : Nat)
    (h : address < base ∨ base + n ≤ address) :
    writeBytes m base word n (.byte address) = m (.byte address) := by
  induction n generalizing m base word with
  | zero => rfl
  | succ n ih =>
    have hn : address < base + 1 ∨ base + 1 + n ≤ address := by omega
    rw [writeBytes, ih _ _ _ hn]
    have hne : address ≠ base := by omega
    simp [write, hne]

@[simp] theorem writeBytes_local (m : Memory) (base word count frame index : Nat) :
    writeBytes m base word count (.local frame index) = m (.local frame index) := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih =>
    rw [writeBytes, ih]
    simp [write]
theorem writeBytes_append (m : Memory) (base word low high : Nat) :
    writeBytes m base word (low + high) =
      writeBytes (writeBytes m base word low) (base + low) (word / 256^low) high := by
  induction low generalizing m base word with
  | zero => simp [writeBytes]
  | succ low ih =>
    simp only [Nat.succ_add, writeBytes, ih, Nat.pow_succ,
      Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm 256 (256^low)]
    congr 1 <;> omega

theorem writeBytes_mod (m : Memory) (base word count : Nat) :
    writeBytes m base (word % 256^count) count = writeBytes m base word count := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih =>
    have low : BitVec.ofNat 8 (word % 256^(count+1)) = BitVec.ofNat 8 word := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.pow_succ]
      exact Nat.mod_mul_left_mod word (256^count) 256
    simp only [writeBytes]
    rw [low]
    simp only [Nat.pow_succ, Nat.mod_mul_left_div_self]
    exact ih _ _ _
theorem writeBytes_congr (m n : Memory)
    (h : ∀ address, m (.byte address) = n (.byte address)) (base word count : Nat) :
    ∀ address, writeBytes m base word count (.byte address) =
      writeBytes n base word count (.byte address) := by
  induction count generalizing m n base word with
  | zero => exact h
  | succ count ih =>
    apply ih
    intro address
    simp only [write]
    split <;> simp_all

@[simp] theorem read64_write_local_byte (m : Memory) (frame index base : Nat) (v : Value) :
    read64 (write m (.local frame index) v) (.byte base) = read64 m (.byte base) := by
  simp [read64]

@[simp] theorem read64_initLocals_byte (m : Memory) (frame base : Nat) (values : List Value) :
    read64 (initLocals m frame values) (.byte base) = read64 m (.byte base) := by
  simp [read64]

theorem write_local_read_local (m : Memory) (frame index otherFrame otherIndex : Nat)
    (v : Value) :
    write m (.local frame index) v (.local otherFrame otherIndex) =
      if otherFrame = frame ∧ otherIndex = index then some v else m (.local otherFrame otherIndex) := by
  simp [write]

@[simp] theorem write_local_read_byte (m : Memory) (frame index address : Nat) (v : Value) :
    write m (.local frame index) v (.byte address) = m (.byte address) := by
  simp [write]

theorem write_byte_local_commute (m : Memory) (base frame index : Nat) (byte v : Value) :
    write (write m (.local frame index) v) (.byte base) byte =
      write (write m (.byte base) byte) (.local frame index) v := by
  funext address
  simp only [write]
  by_cases hb : address = .byte base <;> by_cases hl : address = .local frame index
  all_goals simp_all

@[simp] theorem writeBytes_write_local (m : Memory) (base word count frame index : Nat) (v : Value) :
    writeBytes (write m (.local frame index) v) base word count =
      write (writeBytes m base word count) (.local frame index) v := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih =>
    rw [writeBytes, write_byte_local_commute, ih]
    rfl

end UInt256Proof
