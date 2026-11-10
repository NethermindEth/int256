import UInt256.Methods.AddSubtract.RippleState
import UInt256.Arithmetic.Borrow
import CIL.Safety.WordLocals
import CIL.Safety.StepComposition
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow
import CIL.Safety.ReturnMemory
import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.CallComposition
import UInt256.Safety.CallerSetup
import UInt256.Safety.LimbAccess
import UInt256.Safety.PrivateCalls
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Subtract.BorrowRun

namespace UInt256Proof.Subtract.Profile

open CIL.Safety

-- SubtractWithBorrow: frameless; writes the difference, then the outgoing borrow.
def borrowBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := false, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 3,
  .arg 0,
  .arg 1,
  .sub,
  .arg 2,
  .load64,
  .sub,
  .store64,
  .arg 2,
  .arg 0,
  .arg 1,
  .ltu,
  .convI8,
  .arg 2,
  .load64,
  .arg 0,
  .arg 1,
  .eq,
  .convI8,
  .band,
  .bor,
  .store64,
  .ret] }

theorem borrowBody_shape {profile : CIL.FeatureProfile} : BorrowShape (borrowBody profile) := ⟨rfl, rfl, rfl, rfl⟩

/-- The production borrow word: `a < b`, or an incoming borrow when `a = b`. -/
def borrowWord (a b c : BitVec 64) : BitVec 64 :=
  (if a < b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64 |||
    (c &&& (if a = b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

theorem borrowWord_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    borrowWord a b c = UInt256Proof.borrow a b c := by
  simpa only [borrowWord, UInt256Proof.extend_subtract_choice] using
    UInt256Proof.borrow_expression a b c incoming

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}
open CIL.Safety

/-- Symbolic execution of the frameless borrow body over its two checked writes. -/
theorem borrow_run_of_memory_steps (found : program[index]? = some (borrowBody profile)) :
    BorrowRun program index (borrowBody profile) borrowWord := by
  intro a b c borrow output frame memory stored final borrowFormed outputFormed borrowStored beforeRead
    afterRead resultWrite borrowWrite
  change run program 24 index 0 _ frame [] memory = _
  cil_checked_steps [borrowFormed, outputFormed, borrowStored, beforeRead, afterRead, resultWrite, borrowWrite,
    borrowWord, formValue, instruction, storeValue, referenceAt]

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}
open CIL.Safety UInt256Model.Safety

/-- Independent arithmetic and actual byte readbacks; `Confined` carries the memory guarantee. -/
structure BorrowPost (a b c : BitVec 64) (borrowRef output : Reference) (after : Memory) : Prop where
  outputBytes : read after output 8 1 = .ok (numberBytes (a - b - c).toNat 8)
  borrowBytes : read after borrowRef 8 1 = .ok (numberBytes (UInt256Proof.borrow a b c).toNat 8)
  borrowBound : (UInt256Proof.borrow a b c).toNat ≤ 1
  arithmetic : a.toNat + 2^64 * (UInt256Proof.borrow a b c).toNat = b.toNat + c.toNat + (a - b - c).toNat

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
variable {program : CIL.Program}
open CIL.Safety UInt256Model.Safety

/-- Mathematical borrow recurrence over the four initial operand limbs. -/
def scalarBorrowValue (memory : CIL.Safety.Memory) (left right : Reference) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => if h : n < 4 then
      UInt256Proof.borrow (inputLimb memory left ⟨n, h⟩) (inputLimb memory right ⟨n, h⟩)
        (scalarBorrowValue memory left right n)
    else 0

/-- Subtraction borrows and difference limbs instantiate shared private ripple-call evidence. -/
abbrev ScalarBorrowState (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference)
    (done : Nat) (borrowIndex : Nat := 1) (resultBase : Nat := 2) : Prop :=
  UInt256Proof.AddSubtract.Safety.RippleState program original current frame left right output
    borrowHome results (scalarBorrowValue original left right)
    (fun i => inputLimb original left i - inputLimb original right i -
      scalarBorrowValue original left right i.val) done borrowIndex resultBase

/-- The checked helper updates both outputs and preserves every other remembered result. -/
theorem ScalarBorrowState.advance {original before after : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} {borrowIndex resultBase : Nat} (index : Fin 4)
    (state : ScalarBorrowState (program := program) original before frame left right output borrowHome results index.val borrowIndex resultBase)
    (math : BorrowPost (inputLimb original left index) (inputLimb original right index)
      (scalarBorrowValue original left right index.val) borrowHome (results index) after)
    (formed : after.WellFormed)
    (world : StaticWorldPreserved program before after)
    (framed : Confined [(borrowHome, 8), (results index, 8)] before after) :
    ScalarBorrowState (program := program) original after frame left right output borrowHome results (index.val + 1) borrowIndex resultBase := by
  apply UInt256Proof.AddSubtract.Safety.RippleState.advance index state ?_ ?_
    math.outputBytes formed world framed
  · simpa only [scalarBorrowValue, dite_eq_left index.isLt] using math.borrowBytes
  · simpa only [scalarBorrowValue, dite_eq_left index.isLt] using math.borrowBound

def scalarUnderflowFlag (borrow : BitVec 64) : BitVec 32 :=
  if BitVec.ofNat 64 0 < borrow then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

def scalarDifferenceWord (memory : CIL.Safety.Memory) (left right : Reference) (i : Fin 4) : BitVec 64 :=
  inputLimb memory left i - inputLimb memory right i - scalarBorrowValue memory left right i.val

theorem scalar_difference_words (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarDifferenceWord memory left right = UInt256Proof.differenceWords (inputLimb memory left) (inputLimb memory right) := by
  funext i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [scalarDifferenceWord, scalarBorrowValue, UInt256Proof.differenceWords, show (3 : Fin 4).val = 3 from rfl]

/-- The four borrow-chain words denote the independent 256-bit difference. -/
def scalarDifferenceValue (memory : CIL.Safety.Memory) (left right : Reference) : BitVec 256 :=
  let w := scalarDifferenceWord memory left right
  BitVec.ofNat 256 ((w 0).toNat + (w 1).toNat * 2^64 + (w 2).toNat * 2^128 + (w 3).toNat * 2^192)

theorem scalar_difference_value (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarDifferenceValue memory left right = inputValue memory left - inputValue memory right := by
  change UInt256Model.value (scalarDifferenceWord memory left right) = _
  rw [scalar_difference_words, UInt256Proof.four_limb_difference]
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [leftValue, rightValue]

/-- The returned flag denotes underflow of the initial mathematical operands. -/
theorem scalar_flag_underflow (memory : Memory) (left right : Reference) :
    scalarUnderflowFlag (scalarBorrowValue memory left right 4) =
      (if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0) := by
  have same : scalarBorrowValue memory left right 4 =
      UInt256Proof.Reporting.finalBorrow (inputLimb memory left) (inputLimb memory right) := rfl
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  have underflow := UInt256Proof.Reporting.finalBorrow_underflow (inputLimb memory left) (inputLimb memory right)
  simp only [BitVec.ofNat_eq_ofNat, leftValue, rightValue] at underflow
  simp only [scalarUnderflowFlag, same, UInt256Proof.Reporting.word_positive,
    underflow, BitVec.ofNat_eq_ofNat]

end UInt256Proof.Subtract.Profile
