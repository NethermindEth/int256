import CIL.Memory

namespace CIL

/-- Allocation invalidates all previous bytes in the reused private home.
    Unknown fields remain absent until the actual body writes them. -/
def clearHome (m : Memory) (frame kind index : Nat) : Memory :=
  fun address => match address with
  | .home f k i offset => if f = frame ∧ k = kind ∧ i = index ∧ offset < 32 then none else m address
  | _ => m address

def readAggregate (m : Memory) (frame kind index : Nat) : Option Value := do
  return .v256 (BitVec.ofNat 256 (← readHomeBytes m frame kind index 0 32))

def writeAggregate (m : Memory) (frame kind index : Nat) (bits : BitVec 256) : Memory :=
  writeHomeBytes m frame kind index 0 bits.toNat 32

@[simp] theorem clearHome_caller (m : Memory) (frame kind index address : Nat) :
    clearHome m frame kind index (.byte address) = m (.byte address) := by rfl

@[simp] theorem writeHomeBytes_caller (m : Memory)
    (frame kind index offset value count address : Nat) :
    writeHomeBytes m frame kind index offset value count (.byte address) = m (.byte address) := by
  induction count generalizing m offset value with
  | zero => rfl
  | succ count ih => simp [writeHomeBytes, ih, write]

@[simp] theorem readAggregate_uninitialized (m : Memory) (frame kind index : Nat) :
    readAggregate (clearHome m frame kind index) frame kind index = none := by
  simp [readAggregate, readHomeBytes, clearHome]

theorem writeHomeBytes_outside (m : Memory) (frame kind index offset value count address : Nat)
    (h : address < offset ∨ offset + count ≤ address) :
    writeHomeBytes m frame kind index offset value count (.home frame kind index address) =
      m (.home frame kind index address) := by
  induction count generalizing m offset value with
  | zero => rfl
  | succ count ih =>
    rw [writeHomeBytes, ih _ _ _ (by omega)]
    simp only [write]
    split
    · rename_i he
      have : address = offset := by cases he; rfl
      omega
    · rfl

theorem readHomeBytes_after_write (m : Memory) (frame kind index offset number count : Nat) :
    readHomeBytes (writeHomeBytes m frame kind index offset number count)
      frame kind index offset count = some (number % 256^count) := by
  induction count generalizing m offset number with
  | zero => simp only [readHomeBytes, Nat.pow_zero, Nat.mod_one]
  | succ count ih =>
    rw [writeHomeBytes, readHomeBytes]
    rw [writeHomeBytes_outside _ frame kind index (offset + 1) (number / 256) count offset
      (Or.inl (by omega))]
    simp only [write, ↓reduceIte]
    rw [ih]
    simp only [Nat.pow_succ]
    change some (number % 256 + 256 * (number / 256 % 256^count)) =
      some (number % (256^count * 256))
    congr 1
    simpa only [Nat.mod_mul_left_mod, Nat.mod_mul_left_div_self] using
      Nat.mod_add_div (number % (256^count * 256)) 256

@[simp] theorem aggregate_snapshot_after_write (m : Memory)
    (frame kind index : Nat) (bits : BitVec 256) :
    readAggregate (writeAggregate m frame kind index bits) frame kind index = some (.v256 bits) := by
  simp only [readAggregate, writeAggregate, readHomeBytes_after_write,
    show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt bits.isLt]
  simp

theorem readHomeBytes_write_disjoint (m : Memory)
    (frame kind index writtenOffset number writtenCount offset count : Nat)
    (h : offset + count ≤ writtenOffset ∨ writtenOffset + writtenCount ≤ offset) :
    readHomeBytes (writeHomeBytes m frame kind index writtenOffset number writtenCount)
      frame kind index offset count = readHomeBytes m frame kind index offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [readHomeBytes, readHomeBytes,
      writeHomeBytes_outside _ frame kind index writtenOffset number writtenCount offset (by omega),
      ih (offset + 1) (by omega)]

theorem readHomeBytes_append (m : Memory) (frame kind index offset low high : Nat) :
    readHomeBytes m frame kind index offset (low + high) = do
      let lo ← readHomeBytes m frame kind index offset low
      let hi ← readHomeBytes m frame kind index (offset + low) high
      return lo + 256^low * hi := by
  induction low generalizing offset with
  | zero => simp [readHomeBytes]
  | succ low ih =>
    rw [Nat.succ_add, readHomeBytes]
    cases cell : m (.home frame kind index offset) with
    | none => simp [cell, readHomeBytes]
    | some value =>
      cases value <;> simp only [cell, readHomeBytes]
      all_goals try rfl
      case i8 lo =>
        rw [ih]
        have offsets : offset + 1 + low = offset + (low + 1) := by omega
        rw [offsets]
        cases tail : readHomeBytes m frame kind index (offset + 1) low <;>
          cases highBytes : readHomeBytes m frame kind index (offset + (low + 1)) high <;>
          simp [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
            Nat.mul_comm 256]

def storeHomeWords (m : Memory) (frame kind index : Nat) (r0 r1 r2 r3 : W64) : Memory :=
  writeHomeBytes (writeHomeBytes (writeHomeBytes (writeHomeBytes m
    frame kind index 0 r0.toNat 8) frame kind index 8 r1.toNat 8)
    frame kind index 16 r2.toNat 8) frame kind index 24 r3.toNat 8

theorem readAggregate_storeHomeWords (m : Memory) (frame kind index : Nat)
    (r0 r1 r2 r3 : W64) :
    readAggregate (storeHomeWords m frame kind index r0 r1 r2 r3) frame kind index =
      some (.v256 (BitVec.ofNat 256
        (r0.toNat + r1.toNat * 2^64 + r2.toNat * 2^128 + r3.toNat * 2^192))) := by
  unfold readAggregate
  rw [show 32 = 8 + 24 from rfl, readHomeBytes_append]
  rw [show 24 = 8 + 16 from rfl, readHomeBytes_append]
  rw [show 16 = 8 + 8 from rfl, readHomeBytes_append]
  simp only [Nat.reduceAdd]
  simp [storeHomeWords, readHomeBytes_write_disjoint, readHomeBytes_after_write,
    Nat.mod_eq_of_lt r0.isLt, Nat.mod_eq_of_lt r1.isLt,
    Nat.mod_eq_of_lt r2.isLt, Nat.mod_eq_of_lt r3.isLt]
  congr 1
  simp only [Nat.mul_add]
  omega

end CIL
