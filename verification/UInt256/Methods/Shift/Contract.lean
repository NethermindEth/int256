import CIL.Semantics
import UInt256.Representation

open CIL UInt256Model

namespace UInt256Proof.Shift

inductive Direction where
  | left | right
  deriving DecidableEq

/-- Public full-Int32 count behavior, including the documented historic negative
    convention. `none` denotes a zero result rather than an exception. -/
def effectiveCount (count : W32) : Option Nat :=
  if count.toInt < 0 then
    if count.toNat % 64 = 0 then none else some (count.toNat % 64)
  else if count.toNat < 256 then some count.toNat else none

def result (direction : Direction) (initial : BitVec 256) (count : W32) : BitVec 256 :=
  match effectiveCount count with
  | none => 0
  | some n => match direction with
    | .left => initial <<< n
    | .right => initial >>> n

theorem effectiveCount_nonnegative (count : W32) (nonnegative : 0 ≤ count.toInt)
    (small : count.toNat < 256) : effectiveCount count = some count.toNat := by
  simp [effectiveCount, show ¬count.toInt < 0 by omega, small]

theorem effectiveCount_large (count : W32) (nonnegative : 0 ≤ count.toInt)
    (large : 256 ≤ count.toNat) : effectiveCount count = none := by
  simp [effectiveCount, show ¬count.toInt < 0 by omega, show ¬count.toNat < 256 by omega]

theorem effectiveCount_negative_zero (count : W32) (negative : count.toInt < 0)
    (multiple : count.toNat % 64 = 0) : effectiveCount count = none := by
  simp [effectiveCount, negative, multiple]

theorem effectiveCount_negative (count : W32) (negative : count.toInt < 0)
    (nonmultiple : count.toNat % 64 ≠ 0) : effectiveCount count = some (count.toNat % 64) := by
  simp [effectiveCount, negative, nonmultiple]

theorem effectiveCount_bound (count : W32) (n : Nat) (selected : effectiveCount count = some n) :
    n < 256 := by
  unfold effectiveCount at selected
  split at selected
  · split at selected
    · contradiction

    · have bound := Nat.mod_lt count.toNat (show 0 < 64 by decide)
      simp only [Option.some.injEq] at selected
      omega
  · split at selected
    · simp only [Option.some.injEq] at selected
      omega
    · contradiction

theorem signed_count_mod64 (count : W32) :
    (count.toInt % 64).toNat = count.toNat % 64 := by
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- Independent mathematical result on the initial operand, normal finite
    execution, and equality of every caller byte with the exact output update. -/
def Contract (direction : Direction) (program : Program) (entry : Nat)
    (initial : Bytes) (input out : Nat) (count : W32) : Prop :=
  ∃ fuel final,
    invoke program fuel entry [.object input, .i32 count, .object out]
      (byteMemory initial) = some (final, []) ∧
    ∀ address, final (.byte address) =
      (writeBytes (byteMemory initial) out
        (result direction (byteValue initial input) count).toNat 32) (.byte address)

end UInt256Proof.Shift
