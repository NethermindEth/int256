import UInt256.Arithmetic.Carry
import CIL.Safety.WordLocals
import CIL.Safety.StepComposition
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow
import CIL.Safety.ReturnMemory
import CIL.Safety.ExecutionStaticWorld
import UInt256.Safety.CallerSetup
import UInt256.Safety.LimbAccess
import UInt256.Methods.Add.SafetyResult
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Add.CarryRun
import CIL.Safety.MethodContract
import UInt256.Safety.PrivateCalls
namespace UInt256Proof.Add.CarrySafety
def carryBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := false, locals := [.i64 0, .i64 0], localKinds := [.word64, .word64], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .arg 1,
  .add,
  .setLocal 0,
  .local 0,
  .arg 2,
  .load64,
  .add,
  .setLocal 1,
  .arg 2,
  .local 0,
  .arg 0,
  .ltu,
  .convI8,
  .local 1,
  .local 0,
  .ltu,
  .convI8,
  .add,
  .store64,
  .arg 3,
  .local 1,
  .store64,
  .ret] }

theorem carryBody_shape {profile : CIL.FeatureProfile} : CarryShape (carryBody profile) := ⟨rfl, rfl, rfl, rfl⟩
end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety

def carryWord (a b c : BitVec 64) : BitVec 64 :=
  ((if a + b < a then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64) +
  ((if a + b + c < a + b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

/-- Symbolic execution of the carry body with explicit checked memory transitions. -/
theorem carry_run_of_memory_steps (found : program[index]? = some (carryBody profile)) (a b c : BitVec 64) (carry output first second : Reference)
    (frame : Frame) (m0 m1 m2 m3 m4 : Memory)
    (locals : frame.locals = [.bytes .word64 first, .bytes .word64 second])
    (s0 : storeLocal m0 (.bytes .word64 first) (.scalar (.i64 (a + b))) =
      .ok (.bytes .word64 first, m1))
    (s1 : storeLocal m1 (.bytes .word64 second) (.scalar (.i64 (a + b + c))) =
      .ok (.bytes .word64 second, m2))
    (r0 : loadLocal m1 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))))
    (rc : loadValue m1 (.address carry) 8 = .ok (.i64 c))
    (r1 : loadLocal m2 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))))
    (r2 : loadLocal m2 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))))
    (r3 : loadLocal m3 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))))
    (fc1 : form m1 carry = .ok carry) (fc2 : form m2 carry = .ok carry)
    (fo3 : form m3 output = .ok output)
    (wc : write m2 carry (numberBytes (carryWord a b c).toNat 8) 1 = .ok m3)
    (wo : write m3 output (numberBytes (a + b + c).toNat 8) 1 = .ok m4) :
    run program ((carryBody profile).code.length + 1)
      index 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
      frame [] m0 = .ok (leaveFrame frame m4, []) := by
  simp [carryWord, BitVec.toNat_add] at wc
  simp [BitVec.toNat_add] at wo
  change run program 25 index 0 _ frame [] m0 = _
  iterate 23
    apply Eq.trans
    · apply run_next found (by rfl)
      first | rfl | simp
        [step, locals, s0, s1, r0, rc, r1, r2, r3,
          checkedValue, formValue, fc1, fc2, fo3,
          pureArity.eq_def, instruction.eq_def, storeValue,
          referenceAt, wc, wo, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure] <;> first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  rw [run]
  simp [found, carryBody, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms carry_run_of_memory_steps

end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety

end UInt256Proof.Add.CarrySafety


namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

theorem carryWord_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    carryWord a b c = UInt256Proof.carry a b c := by
  simp only [carryWord, UInt256Proof.extend_choice]
  have h := UInt256Proof.carry_expression a b c incoming
  change ((if a + b < a then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) +
    (if a + b + c < a + b then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) = _ at h
  exact h

theorem carryWord_arithmetic (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    (a + b + c).toNat + 2^64 * (carryWord a b c).toNat = a.toNat + b.toNat + c.toNat ∧
      (carryWord a b c).toNat ≤ 1 := by
  rw [carryWord_correct a b c incoming]
  exact ⟨UInt256Proof.carry_word_nat a b c incoming, UInt256Proof.carry_bound a b c incoming⟩

#print axioms carryWord_correct
#print axioms carryWord_arithmetic

end UInt256Proof.Add.CarrySafety


namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety

/-- Independent arithmetic and actual byte readbacks; `Confined` carries the memory guarantee. -/
structure CarryPost (a b c : BitVec 64) (carryRef output : Reference) (after : Memory) : Prop where
  outputBytes : read after output 8 1 = .ok (numberBytes (a + b + c).toNat 8)
  carryBytes : read after carryRef 8 1 = .ok (numberBytes (UInt256Proof.carry a b c).toNat 8)
  carryBound : (UInt256Proof.carry a b c).toNat ≤ 1
  arithmetic : (a + b + c).toNat + 2^64 * (UInt256Proof.carry a b c).toNat = a.toNat + b.toNat + c.toNat

end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}
open CIL.Safety UInt256Model.Safety

/-- Mathematical carry recurrence over the four initial operand limbs. -/
def scalarCarryValue (memory : CIL.Safety.Memory) (left right : Reference) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => if h : n < 4 then
      UInt256Proof.carry (inputLimb memory left ⟨n, h⟩) (inputLimb memory right ⟨n, h⟩)
        (scalarCarryValue memory left right n)
    else 0

structure ScalarCarryState (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference) (done : Nat) (carryIndex : Nat := 2) (resultBase : Nat := 3) : Prop where
  call : CallingConditions program current [left, right] [output]
  inputBytes : ∀ reference ∈ [left, right],
    (fun offset => (current.cells reference.allocation offset).bits) =
      (fun offset => (original.cells reference.allocation offset).bits)
  carrySlot : frame.locals[carryIndex]? = some (.bytes .word64 carryHome)
  resultSlots : ∀ i, frame.locals[i.val + resultBase]? = some (.bytes .word64 (results i))
  carryWrite : access current carryHome 8 1 true = .ok ()
  resultWrites : ∀ i, access current (results i) 8 1 true = .ok ()
  carryRead : read current carryHome 8 1 = .ok (numberBytes (scalarCarryValue original left right done).toNat 8)
  carryBound : (scalarCarryValue original left right done).toNat ≤ 1
  callerSeparate : ∀ reference ∈ [left, right],
    reference.allocation ≠ carryHome.allocation ∧ ∀ i, reference.allocation ≠ (results i).allocation
  carrySeparate : ∀ i, (results i).allocation ≠ carryHome.allocation
  resultSeparate : ∀ i j, i ≠ j → (results i).allocation ≠ (results j).allocation
  carryFresh : original.nextIdentity ≤ carryHome.allocation
  resultsFresh : ∀ i, original.nextIdentity ≤ (results i).allocation
  callerCells : ∀ id, id < original.nextIdentity → ∀ offset,
    current.cells id offset = original.cells id offset
  completed : ∀ i, i.val < done → read current (results i) 8 1 =
    .ok (numberBytes (inputLimb original left i + inputLimb original right i +
      scalarCarryValue original left right i.val).toNat 8)

/-- A checked carry call advances the parent invariant, keeping inputs and completed words. -/
theorem ScalarCarryState.advance {original before after : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} {carryIndex resultBase : Nat} (index : Fin 4)
    (state : ScalarCarryState (program := program) original before frame left right output carryHome results index.val carryIndex resultBase)
    (math : CarryPost (inputLimb original left index) (inputLimb original right index)
      (scalarCarryValue original left right index.val) carryHome (results index) after)
    (formed : after.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) before →
      StaticWorldValid (programStaticDescriptors program) after)
    (framed : Confined [(carryHome, 8), (results index, 8)] before after) :
    ScalarCarryState (program := program) original after frame left right output carryHome results (index.val + 1) carryIndex resultBase := by
  have separate : ∀ reference ∈ [left, right],
      reference.allocation ≠ carryHome.allocation ∧ reference.allocation ≠ (results index).allocation :=
    fun reference member => ⟨(state.callerSeparate reference member).1,
      (state.callerSeparate reference member).2 index⟩
  have carryOld : carryHome.allocation < before.nextIdentity := by
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ state.carryWrite
    exact (state.call.1.1.1 _ _ present).1
  have resultOld : ∀ i, (results i).allocation < before.nextIdentity := by
    intro i
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (state.resultWrites i)
    exact (state.call.1.1.1 _ _ present).1
  refine ⟨private_calling_conditions framed formed world state.call separate, ?_, state.carrySlot, state.resultSlots,
    (framed.access_write _ carryOld _ _).trans state.carryWrite,
    fun i => (framed.access_write _ (resultOld i) _ _).trans (state.resultWrites i), ?_, ?_,
    state.callerSeparate, state.carrySeparate, state.resultSeparate,
    state.carryFresh, state.resultsFresh, ?_, ?_⟩
  · intro reference member
    exact (private_input_bytes framed state.call member (separate reference member).1
      (separate reference member).2).trans (state.inputBytes reference member)
  · simpa only [scalarCarryValue, dite_eq_left index.isLt] using math.carryBytes
  · simpa only [scalarCarryValue, dite_eq_left index.isLt] using math.carryBound
  · intro id old offset
    have belowCarry := Nat.lt_of_lt_of_le old state.carryFresh
    have belowResult := Nat.lt_of_lt_of_le old (state.resultsFresh index)
    exact (framed.cells_apart (Nat.lt_trans belowCarry carryOld)
      (by simp [Nat.ne_of_lt belowCarry, Nat.ne_of_lt belowResult]) offset).trans
      (state.callerCells id old offset)
  · intro i done
    by_cases same : i = index
    · subst i
      exact math.outputBytes
    · have earlier : i.val < index.val := by
        have different : i.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      exact framed.read_apart state.call.1.1 (state.completed i earlier)
        (by simp [Apart, state.carrySeparate i, state.resultSeparate i index same])

#print axioms ScalarCarryState.advance

end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

def scalarOverflowFlag (carry : BitVec 64) : BitVec 32 :=
  if BitVec.ofNat 64 0 < carry then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

def scalarSumWord (memory : CIL.Safety.Memory) (left right : Reference) (i : Fin 4) : BitVec 64 :=
  inputLimb memory left i + inputLimb memory right i + scalarCarryValue memory left right i.val

def scalarSumValue (memory : CIL.Safety.Memory) (left right : Reference) : BitVec 256 :=
  let w := scalarSumWord memory left right
  BitVec.ofNat 256 ((w 0).toNat + (w 1).toNat * 2^64 + (w 2).toNat * 2^128 + (w 3).toNat * 2^192)

theorem scalar_sum_words (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarSumWord memory left right = UInt256Proof.sumWords (inputLimb memory left) (inputLimb memory right) := by
  funext i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [scalarSumWord, scalarCarryValue, UInt256Proof.sumWords]

/-- The four ripple words equal the independent 256-bit sum of the initial operands. -/
theorem scalar_sum_value (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarSumValue memory left right = inputValue memory left + inputValue memory right := by
  change UInt256Model.value (scalarSumWord memory left right) = _
  rw [scalar_sum_words, UInt256Proof.sumWords_sum]
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [leftValue, rightValue]

theorem scalar_flag_overflow (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarOverflowFlag (scalarCarryValue memory left right 4) = addOverflow memory left right := by
  have same : scalarCarryValue memory left right 4 =
      UInt256Proof.Reporting.finalCarry (inputLimb memory left) (inputLimb memory right) := rfl
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  have overflow := UInt256Proof.Reporting.finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  simp only [BitVec.ofNat_eq_ofNat, leftValue, rightValue] at overflow
  simp only [scalarOverflowFlag, same, UInt256Proof.Reporting.word_positive,
    overflow, addOverflow, BitVec.ofNat_eq_ofNat]

#print axioms scalar_sum_words
#print axioms scalar_sum_value
#print axioms scalar_flag_overflow
end UInt256Proof.Add.CarrySafety
