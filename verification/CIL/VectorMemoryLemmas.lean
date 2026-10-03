import CIL.VectorMemory
import CIL.MemoryLemmas

open CIL

namespace UInt256Proof

@[simp] theorem byte_cast_bound (value : Nat) : value % 256 % 4294967296 < 256 := by
  have h := Nat.mod_lt value (by decide : 0 < 256)
  have hle := Nat.mod_le (value % 256) 4294967296
  omega

@[simp] theorem unsafeAdd_static_nonnegative (size offset : Nat) (bytes : List (BitVec 8)) :
    CIL.unsafeAdd size (offset : Int) (.static bytes 0) =
      some (.static bytes (size * offset)) := by
  simp [CIL.unsafeAdd, ← Int.natCast_mul]

@[simp ↓] theorem eval_add_static_vector (m : CIL.Memory) (bytes : List (BitVec 8))
    (index : CIL.W32) (rest : List CIL.Value) :
    CIL.evalMemory (.add 32 false)
      (.i64 (index.zeroExtend 64) :: .ref (.static bytes 0) :: rest) m =
      some (m, .ref (.static bytes (32 * index.toNat)) :: rest) := by
  have bound : index.toNat < 2^64 := by have hi := index.isLt; omega
  simp [CIL.evalMemory, CIL.offsetValue, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt bound]

theorem writeBytes_inside (m : Memory) (base word count address : Nat)
    (h : base ≤ address ∧ address < base + count) :
    writeBytes m base word count (.byte address) =
      some (.i8 (BitVec.ofNat 8 (word / 256^(address - base)))) := by
  induction count generalizing m base word with
  | zero => omega
  | succ count ih =>
    by_cases he : address = base
    · subst address
      rw [writeBytes, writeBytes_outside _ (base + 1) _ count base (Or.inl (by omega))]
      simp [write]
    · rw [writeBytes, ih _ (base + 1) (word / 256) (by omega)]
      have shift : address - base = (address - (base + 1)) + 1 := by omega
      rw [shift, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm 256]

@[simp] theorem writeBytes_static (m : Memory) (base word count offset : Nat)
    (bytes : List (BitVec 8)) :
    writeBytes m base word count (.static bytes offset) = m (.static bytes offset) := by
  induction count generalizing m base word with
  | zero => rfl
  | succ count ih => rw [writeBytes, ih]; simp [write]

theorem writeBytes_overwrite_same (m : Memory) (base old new count : Nat) :
    writeBytes (writeBytes m base old count) base new count = writeBytes m base new count := by
  funext address
  cases address with
  | byte address =>
    by_cases h : base ≤ address ∧ address < base + count
    · rw [writeBytes_inside _ _ _ _ _ h, writeBytes_inside _ _ _ _ _ h]
    · have outside : address < base ∨ base + count ≤ address := by omega
      rw [writeBytes_outside _ _ _ _ _ outside,
        writeBytes_outside _ _ _ _ _ outside, writeBytes_outside _ _ _ _ _ outside]
  | «local» frame index => simp
  | static bytes offset => simp
  | home frame kind index offset => simp

theorem readBytes_bound (m : Memory) (base count number : Nat)
    (h : readBytes m base count = some number) : number < 256^count := by
  induction count generalizing base number with
  | zero => simp [readBytes] at h; subst number; decide
  | succ count ih =>
    cases cell : m (.byte base) with
    | none => simp [readBytes, cell] at h
    | some v =>
      cases v <;> simp only [readBytes, cell] at h
      all_goals try contradiction
      case i8 lo =>
        cases tail : readBytes m (base + 1) count with
        | none => simp [tail] at h
        | some hi =>
          have hb := ih (base + 1) hi tail
          have hl := lo.isLt
          simp [tail] at h
          subst number
          simp only [Nat.pow_succ]
          omega

theorem readBytes_of_read64 (m : Memory) (base : Nat) (word : W64)
    (h : read64 m (.byte base) = some (.i64 word)) :
    readBytes m base 8 = some word.toNat := by
  cases bytes : readBytes m base 8 with
  | none => simp [read64, bytes] at h
  | some number =>
    have bound := readBytes_bound m base 8 number bytes
    have hw : BitVec.ofNat 64 number = word := by simpa [read64, bytes] using h
    have hn := congrArg BitVec.toNat hw
    simp only [BitVec.toNat_ofNat] at hn
    change number < 2^64 at bound
    rw [Nat.mod_eq_of_lt bound] at hn
    simp [hn]

theorem readBytes_append_of (m : Memory) (base low high lo hi : Nat)
    (hl : readBytes m base low = some lo)
    (hh : readBytes m (base + low) high = some hi) :
    readBytes m base (low + high) = some (lo + 256^low * hi) := by
  induction low generalizing base lo with
  | zero => simp [readBytes] at hl; subst lo; simpa using hh
  | succ low ih =>
    cases cell : m (.byte base) with
    | none => simp [readBytes, cell] at hl
    | some v =>
      cases v <;> simp only [readBytes, cell] at hl
      all_goals try contradiction
      case i8 byte =>
        cases tail : readBytes m (base + 1) low with
        | none => simp [tail] at hl
        | some rest =>
          have highReads : readBytes m (base + 1 + low) high = some hi := by
            simpa only [Nat.add_assoc, Nat.add_comm 1 low] using hh
          have joined := ih (base + 1) rest tail highReads
          simp [tail] at hl
          subst lo
          simp only [Nat.succ_add, readBytes, cell]
          rw [joined]
          change some (byte.toNat + 256 * (rest + 256^low * hi)) =
            some (byte.toNat + 256 * rest + 256^(low+1) * hi)
          congr 1
          simp [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.mul_left_comm]

theorem readBytes_writeBytes (m : Memory) (base number count : Nat) :
    readBytes (writeBytes m base number count) base count = some (number % 256^count) := by
  induction count generalizing m base number with
  | zero => simp only [readBytes, Nat.pow_zero, Nat.mod_one]
  | succ count ih =>
    rw [writeBytes, readBytes]
    rw [writeBytes_outside _ (base + 1) (number / 256) count base (Or.inl (by omega))]
    simp only [write, ↓reduceIte]
    rw [ih]
    simp only [Nat.pow_succ]
    change some (number % 256 + 256 * (number / 256 % 256^count)) =
      some (number % (256^count * 256))
    congr 1
    simpa only [Nat.mod_mul_left_mod, Nat.mod_mul_left_div_self] using
      Nat.mod_add_div (number % (256^count * 256)) 256

theorem read128_after_write (m : Memory) (base : Nat) (bits : BitVec 128) :
    read128 (writeBytes m base bits.toNat 16) (.byte base) = some (.v128 bits) := by
  simp only [read128, readBytes_writeBytes, show (256 : Nat)^16 = 2^128 from rfl,
    Nat.mod_eq_of_lt bits.isLt]
  simp

theorem read256_after_write (m : Memory) (base : Nat) (bits : BitVec 256) :
    read256 (writeBytes m base bits.toNat 32) (.byte base) = some (.v256 bits) := by
  simp only [read256, readBytes_writeBytes, show (256 : Nat)^32 = 2^256 from rfl,
    Nat.mod_eq_of_lt bits.isLt]
  simp

theorem read128_congr (m n : Memory)
    (h : ∀ address, m (.byte address) = n (.byte address)) (base : Nat) :
    read128 m (.byte base) = read128 n (.byte base) := by
  simp only [read128, readBytes_congr m n h]

theorem read256_congr (m n : Memory)
    (h : ∀ address, m (.byte address) = n (.byte address)) (base : Nat) :
    read256 m (.byte base) = read256 n (.byte base) := by
  simp only [read256, readBytes_congr m n h]

@[simp] theorem read128_write_local (m : Memory) (frame index base : Nat) (v : Value) :
    read128 (write m (.local frame index) v) (.byte base) = read128 m (.byte base) := by
  simp [read128]

@[simp] theorem read256_write_local (m : Memory) (frame index base : Nat) (v : Value) :
    read256 (write m (.local frame index) v) (.byte base) = read256 m (.byte base) := by
  simp [read256]

theorem write128_outside (m : Memory) (base address : Nat) (bits : BitVec 128)
    (h : address < base ∨ base + 16 ≤ address) :
    (writeBytes m base bits.toNat 16) (.byte address) = m (.byte address) :=
  writeBytes_outside m base bits.toNat 16 address h

theorem write256_outside (m : Memory) (base address : Nat) (bits : BitVec 256)
    (h : address < base ∨ base + 32 ≤ address) :
    (writeBytes m base bits.toNat 32) (.byte address) = m (.byte address) :=
  writeBytes_outside m base bits.toNat 32 address h

@[simp] theorem write128_preserves_local (m : Memory) (base frame index : Nat)
    (bits : BitVec 128) :
    writeBytes m base bits.toNat 16 (.local frame index) = m (.local frame index) := by
  simp

@[simp] theorem write256_preserves_local (m : Memory) (base frame index : Nat)
    (bits : BitVec 256) :
    writeBytes m base bits.toNat 32 (.local frame index) = m (.local frame index) := by
  simp

/-- A local containing a captured operand remains unchanged even when the
    output overlaps the original operand's caller bytes. -/
theorem captured256_survives_store (m : Memory) (base frame index : Nat)
    (captured result : BitVec 256) :
    read256 (writeBytes (write m (.local frame index) (.v256 captured))
      base result.toNat 32) (.local frame index) = some (.v256 captured) := by
  simp [read256, write]

theorem captured128_survives_store (m : Memory) (base frame index : Nat)
    (captured result : BitVec 128) :
    read128 (writeBytes (write m (.local frame index) (.v128 captured))
      base result.toNat 16) (.local frame index) = some (.v128 captured) := by
  simp [read128, write]

theorem unsafeAdd_byte_nonnegative (size base offset : Nat) :
    unsafeAdd size (offset : Int) (.byte base) = some (.byte (base + size * offset)) := by
  exact unsafeAdd_byte_natural size base offset

@[simp] theorem unsafeAdd_byte_one (size base : Nat) :
    unsafeAdd size 1 (.byte base) = some (.byte (base + size)) := by
  simpa only [Int.natCast_one, Nat.mul_one] using unsafeAdd_byte_nonnegative size base 1

/-- The abstract calculation agrees with native 64-bit pointer arithmetic
    whenever the caller supplies the usual nonwrapping address bounds. -/
theorem unsafeAdd_native_bound (size base offset : Nat)
    (h : base + size * offset < 2^64) :
    unsafeAdd size (offset : Int) (.byte base) =
      some (.byte ((BitVec.ofNat 64 base + BitVec.ofNat 64 (size * offset)).toNat)) := by
  rw [unsafeAdd_byte_nonnegative]
  congr 2
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end UInt256Proof
