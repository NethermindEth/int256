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
import UInt256.Methods.Reporting.Arithmetic

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

/-- The production borrow word: `a < b`, or an incoming borrow when `a = b`. -/
def borrowWord (a b c : BitVec 64) : BitVec 64 :=
  (if a < b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64 |||
    (c &&& (if a = b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

theorem borrowWord_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    borrowWord a b c = UInt256Proof.borrow a b c := by
  simpa only [borrowWord, UInt256Proof.extend_subtract_choice] using
    UInt256Proof.borrow_expression a b c incoming

#print axioms borrowWord_correct
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}
open CIL.Safety

/-- Symbolic execution of the frameless borrow body over its two checked writes. -/
theorem borrow_run_of_memory_steps (found : program[index]? = some (borrowBody profile)) (a b c : BitVec 64)
    (borrow output : Reference) (frame : Frame) (memory stored final : Memory)
    (borrowFormed : form memory borrow = .ok borrow) (outputFormed : form memory output = .ok output)
    (borrowStored : form stored borrow = .ok borrow)
    (beforeRead : loadValue memory (.address borrow) 8 = .ok (.i64 c))
    (afterRead : loadValue stored (.address borrow) 8 = .ok (.i64 c))
    (resultWrite : write memory output (numberBytes (a - b - c).toNat 8) 1 = .ok stored)
    (borrowWrite : write stored borrow (numberBytes (borrowWord a b c).toNat 8) 1 = .ok final) :
    run program ((borrowBody profile).code.length + 1) index 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrow), .reference (.address output)]
      frame [] memory = .ok (leaveFrame frame final, []) := by
  simp [borrowWord, BitVec.toNat_or, BitVec.toNat_and] at borrowWrite
  simp [BitVec.toNat_sub] at resultWrite
  change run program 24 index 0 _ frame [] memory = _
  iterate 22
    apply Eq.trans
    · apply run_next found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, formValue, borrowFormed, outputFormed,
          borrowStored, beforeRead, afterRead, pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary,
          instruction, storeValue, referenceAt, resultWrite, borrowWrite, checkedAt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  rw [run]
  simp [found, borrowBody, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms borrow_run_of_memory_steps
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}
open CIL.Safety UInt256Model.Safety

/-- Independent arithmetic, actual byte readbacks, and retained caller storage. -/
structure BorrowPost (a b c : BitVec 64) (borrowRef output : Reference) (before after : Memory) : Prop where
  wellFormed : after.WellFormed
  outputBytes : read after output 8 1 = .ok (numberBytes (a - b - c).toNat 8)
  borrowBytes : read after borrowRef 8 1 = .ok (numberBytes (UInt256Proof.borrow a b c).toNat 8)
  borrowBound : (UInt256Proof.borrow a b c).toNat ≤ 1
  arithmetic : a.toNat + 2^64 * (UInt256Proof.borrow a b c).toNat = b.toNat + c.toNat + (a - b - c).toNat
  footprint : ∀ id offset, id < before.nextIdentity → OutsideWord borrowRef id offset → OutsideWord output id offset →
    after.cells id offset = before.cells id offset
  access : AccessBelow before.nextIdentity before after
  staticWorld : StaticWorldValid (programStaticDescriptors program) before →
    StaticWorldValid (programStaticDescriptors program) after

/-- Simultaneous borrow/result readback requires nonoverlapping words. -/
theorem borrow_checked_contract (found : program[index]? = some (borrowBody profile)) (a b c : BitVec 64)
    (borrowRef output : Reference) (memory : Memory)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (readable : read memory borrowRef 8 1 = .ok (numberBytes c.toNat 8))
    (writable : access memory borrowRef 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowRef output) :
    ∃ fuel final,
      invoke program fuel index
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
        memory = .ok (final, []) ∧ BorrowPost (program := program) a b c borrowRef output memory final := by
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨allocation, authority⟩ := access_requirements writable
  obtain ⟨stored, resultWrite⟩ := write_succeeds (bytes := numberBytes (a - b - c).toNat 8)
    (by simpa only [length] using outputWritable)
  have retained := write_preserves_disjoint_read resultWrite readable
    (by simpa only [WordsDisjoint, length] using disjoint)
  have borrowWritable := (authority.after_write resultWrite).access
  obtain ⟨final, borrowWrite⟩ := write_succeeds (bytes := numberBytes (borrowWord a b c).toNat 8)
    (by simpa only [length] using borrowWritable)
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fb := access_reference_valid _ _ _ _ _ writable
  have fo := access_reference_valid _ _ _ _ _ outputWritable
  have run := borrow_run_of_memory_steps found a b c borrowRef output frame memory stored final fb fo
    (access_reference_valid _ _ _ _ _ borrowWritable) (load_word64_of_read readable)
    (load_word64_of_read retained) resultWrite borrowWrite
  simp only [leaveFrame, frame, List.foldl_nil] at run
  have invoked : invoke program ((borrowBody profile).code.length + 1) index
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
      memory = .ok (final, []) := by
    simpa [invoke, found, enterFrame, borrowBody, makeLocals, makeArgumentHomes, makeParameterHomes, frame, checkedValue,
      numericValue, formValue, fb, fo, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure] using run
  refine ⟨_, final, invoked, invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked,
    ?_, ?_, UInt256Proof.borrow_bound a b c, UInt256Proof.borrow_word_nat a b c incoming, ?_,
    (write_preserves_access_below resultWrite memory.nextIdentity).trans
      (write_preserves_access_below borrowWrite memory.nextIdentity),
    fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩
  · have readback : read stored output 8 1 = .ok (numberBytes (a - b - c).toNat 8) := by
      simpa only [length] using write_readback _ _ _ _ _ resultWrite
    apply write_preserves_disjoint_read borrowWrite readback
    rcases disjoint with distinct | before | after
    · exact Or.inl (Ne.symm distinct)
    · exact Or.inr (Or.inr (by simpa only [length] using before))
    · exact Or.inr (Or.inl (by simpa only [length] using after))
  · have readback := write_readback _ _ _ _ _ borrowWrite
    simpa only [length, borrowWord_correct a b c incoming] using readback
  · intro id offset _ outsideBorrow outsideOutput
    rw [write_word_outside borrowWrite id offset outsideBorrow,
      write_word_outside resultWrite id offset outsideOutput]

theorem BorrowPost.private_calling_conditions {a b c : BitVec 64} {borrowRef output : Reference}
    {before after : Memory} (post : BorrowPost (program := program) a b c borrowRef output before after)
    {inputs outputs : List Reference} (call : CallingConditions program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ borrowRef.allocation ∧ reference.allocation ≠ output.allocation) :
    CallingConditions program after inputs outputs := by
  refine ⟨⟨post.wellFormed, ?_, ?_⟩, post.staticWorld call.2⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed inputMember)
    have old := (call.1.1.1 _ _ present).1
    obtain ⟨notBorrow, notOutput⟩ := separate reference inputMember
    refine ⟨_, post.access.read_eq (call.input_snapshot inputMember) old ?_⟩
    intro i _
    exact post.footprint _ _ old (Or.inl notBorrow) (Or.inl notOutput)
  · intro view member
    have writable := call.1.2.2 view member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
    exact post.access.access writable (call.1.1.1 _ _ present).1

theorem BorrowPost.private_input_bytes {a b c : BitVec 64} {borrowRef output : Reference}
    {before after : Memory} (post : BorrowPost (program := program) a b c borrowRef output before after)
    (reference : Reference) (old : reference.allocation < before.nextIdentity)
    (notBorrow : reference.allocation ≠ borrowRef.allocation)
    (notOutput : reference.allocation ≠ output.allocation) :
    (fun offset => (after.cells reference.allocation offset).bits) =
      (fun offset => (before.cells reference.allocation offset).bits) := by
  funext offset
  rw [post.footprint _ _ old (Or.inl notBorrow) (Or.inl notOutput)]

#print axioms borrow_checked_contract
#print axioms BorrowPost.private_calling_conditions
#print axioms BorrowPost.private_input_bytes
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

structure ScalarBorrowState (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference) (done : Nat) (borrowIndex : Nat) (resultBase : Nat) : Prop where
  call : CallingConditions program current [left, right] [output]
  inputBytes : ∀ reference ∈ [left, right],
    (fun offset => (current.cells reference.allocation offset).bits) =
      (fun offset => (original.cells reference.allocation offset).bits)
  borrowSlot : frame.locals[borrowIndex]? = some (.bytes .word64 borrowHome)
  resultSlots : ∀ i, frame.locals[i.val + resultBase]? = some (.bytes .word64 (results i))
  borrowWrite : access current borrowHome 8 1 true = .ok ()
  resultWrites : ∀ i, access current (results i) 8 1 true = .ok ()
  borrowRead : read current borrowHome 8 1 = .ok (numberBytes (scalarBorrowValue original left right done).toNat 8)
  borrowBound : (scalarBorrowValue original left right done).toNat ≤ 1
  callerSeparate : ∀ reference ∈ [left, right],
    reference.allocation ≠ borrowHome.allocation ∧ ∀ i, reference.allocation ≠ (results i).allocation
  borrowSeparate : ∀ i, (results i).allocation ≠ borrowHome.allocation
  resultSeparate : ∀ i j, i ≠ j → (results i).allocation ≠ (results j).allocation
  borrowFresh : original.nextIdentity ≤ borrowHome.allocation
  resultsFresh : ∀ i, original.nextIdentity ≤ (results i).allocation
  callerCells : ∀ id, id < original.nextIdentity → ∀ offset,
    current.cells id offset = original.cells id offset
  completed : ∀ i, i.val < done → read current (results i) 8 1 =
    .ok (numberBytes (inputLimb original left i - inputLimb original right i -
      scalarBorrowValue original left right i.val).toNat 8)

/-- A checked borrow call advances the parent invariant, keeping inputs and completed words. -/
theorem ScalarBorrowState.advance {original before after : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} {borrowIndex resultBase : Nat} (index : Fin 4)
    (state : ScalarBorrowState (program := program) original before frame left right output borrowHome results index.val borrowIndex resultBase)
    (math : BorrowPost (program := program) (inputLimb original left index) (inputLimb original right index)
      (scalarBorrowValue original left right index.val) borrowHome (results index) before after) :
    ScalarBorrowState (program := program) original after frame left right output borrowHome results (index.val + 1) borrowIndex resultBase := by
  have separate : ∀ reference ∈ [left, right],
      reference.allocation ≠ borrowHome.allocation ∧ reference.allocation ≠ (results index).allocation :=
    fun reference member => ⟨(state.callerSeparate reference member).1,
      (state.callerSeparate reference member).2 index⟩
  have borrowOld : borrowHome.allocation < before.nextIdentity := by
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ state.borrowWrite
    exact (state.call.1.1.1 _ _ present).1
  have resultOld : ∀ i, (results i).allocation < before.nextIdentity := by
    intro i
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (state.resultWrites i)
    exact (state.call.1.1.1 _ _ present).1
  refine ⟨math.private_calling_conditions state.call separate, ?_, state.borrowSlot, state.resultSlots,
    math.access.access state.borrowWrite borrowOld,
    fun i => math.access.access (state.resultWrites i) (resultOld i), ?_, ?_,
    state.callerSeparate, state.borrowSeparate, state.resultSeparate,
    state.borrowFresh, state.resultsFresh, ?_, ?_⟩
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (state.call.input_formed member)
    exact (math.private_input_bytes reference (state.call.1.1.1 _ _ present).1 (separate reference member).1
      (separate reference member).2).trans (state.inputBytes reference member)
  · simpa only [scalarBorrowValue, dite_eq_left index.isLt] using math.borrowBytes
  · simpa only [scalarBorrowValue, dite_eq_left index.isLt] using math.borrowBound
  · intro id old offset
    have belowBorrow := Nat.lt_of_lt_of_le old state.borrowFresh
    have belowResult := Nat.lt_of_lt_of_le old (state.resultsFresh index)
    exact (math.footprint id offset (Nat.lt_trans belowBorrow borrowOld)
      (Or.inl (Nat.ne_of_lt belowBorrow)) (Or.inl (Nat.ne_of_lt belowResult))).trans
      (state.callerCells id old offset)
  · intro i done
    by_cases same : i = index
    · subst i
      exact math.outputBytes
    · have earlier : i.val < index.val := by
        have different : i.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      apply math.access.read_eq (state.completed i earlier) (resultOld i)
      intro offset _
      exact math.footprint _ _ (resultOld i) (Or.inl (state.borrowSeparate i))
        (Or.inl (state.resultSeparate i index same))

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

#print axioms ScalarBorrowState.advance
#print axioms scalar_difference_words
#print axioms scalar_difference_value
#print axioms scalar_flag_underflow
end UInt256Proof.Subtract.Profile
