import UInt256.Methods.Add.ARMSmallStateFinish
import UInt256.Arithmetic.Carry
import UInt256.Methods.Reporting.Arithmetic
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armIncrementWord (words : Fin 4 → BitVec 64) (index : Fin 4) : Fin 4 → BitVec 64 :=
  fun i => if i = index then words index + 1 else words i

def armCarryResult (words : Fin 4 → BitVec 64) : (Fin 4 → BitVec 64) × BitVec 32 :=
  let first := armIncrementWord words 1
  if first 1 = BitVec.ofNat 64 0 then
    let second := armIncrementWord first 2
    if second 2 = BitVec.ofNat 64 0 then
      let third := armIncrementWord second 3
      (third, if third 3 = BitVec.ofNat 64 0 then 1 else 0)
    else (second, 0)
  else (first, 0)

/-- Compose all three actual carry paths to their common output entry. The
    resulting values and flag remain explicit for independent arithmetic binding. -/
theorem ARMSmallState.carry (enabled : Extracted.profile.advSimd = true)
    {original entered current : Memory} {input output : Reference} {frame : Frame}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : ARMSmallState original entered current input output frame words sum 0)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ARMSmallState original entered after input output frame (armCarryResult words).1 sum
        (armCarryResult words).2 →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 47 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 23 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  let first := armIncrementWord words 1
  let second := armIncrementWord first 2
  let third := armIncrementWord second 3
  apply state.increment enabled 0 args enteredWF homes post
  intro after1 state1
  change ARMSmallState original entered after1 input output frame first sum 0 at state1
  apply arm_small_increment_branch enabled 0 after1 frame args (first 1) post
  by_cases carry1 : first 1 = BitVec.ofNat 64 0
  · simp only [carry1, ite_true]
    apply state1.increment enabled 1 args enteredWF homes post
    intro after2 state2
    change ARMSmallState original entered after2 input output frame second sum 0 at state2
    apply arm_small_increment_branch enabled 1 after2 frame args (second 2) post
    by_cases carry2 : second 2 = BitVec.ofNat 64 0
    · simp only [carry2, ite_true]
      apply state2.increment enabled 2 args enteredWF homes post
      intro after3 state3
      change ARMSmallState original entered after3 input output frame third sum 0 at state3
      apply state3.final_flag enabled args enteredWF homes post
      intro after updated
      apply continuation after
      simpa only [armCarryResult, show armIncrementWord words 1 = first from rfl,
        carry1, ite_true, show armIncrementWord first 2 = second from rfl,
        carry2] using updated
    · simp only [carry2, ite_false]
      apply continuation after2
      simpa only [armCarryResult, show armIncrementWord words 1 = first from rfl,
        carry1, ite_true, show armIncrementWord first 2 = second from rfl,
        carry2, ite_false] using state2
  · simp only [carry1, ite_false]
    apply continuation after1
    simpa only [armCarryResult, show armIncrementWord words 1 = first from rfl,
      carry1, ite_false] using state1


def armSmallResult (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    (Fin 4 → BitVec 64) × BitVec 32 :=
  if words 0 + word < words 0 then armCarryResult words else (words, 0)

/-- Join no-carry and every carry path using the actual saved low-word comparison. -/
theorem ARMSmallReady.compute (enabled : Extracted.profile.advSimd = true)
    {original entered current : Memory} {input output : Reference} {frame : Frame} {word : BitVec 64}
    (ready : ARMSmallReady original entered current input output word frame)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ARMSmallState original entered after input output frame
        (armSmallResult (inputLimb original input) word).1 (inputLimb original input 0 + word)
        (armSmallResult (inputLimb original input) word).2 →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 47 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 20 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨lowHome, lowSlot, lowRead⟩ := ready.saved.completed 0 (by decide)
  obtain ⟨sumHome, sumSlot, sumRead⟩ := ready.sum
  apply arm_small_low_decision enabled current frame args lowHome sumHome
    (inputLimb original input 0) (inputLimb original input 0 + word)
    lowSlot sumSlot lowRead sumRead post
  by_cases carry : inputLimb original input 0 + word < inputLimb original input 0
  · simp only [carry, ite_true]
    apply ready.state.carry enabled args enteredWF homes post
    intro after state
    apply continuation after
    simpa only [armSmallResult, carry, ite_true] using state
  · simp only [carry, ite_false]
    apply continuation current
    simpa only [armSmallResult, carry, ite_false] using ready.state

/-- Full helper entry through arithmetic and all carry decisions, ready for output. -/
theorem arm_small_computed_prefix (enabled : Extracted.profile.advSimd = true)
    (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ARMSmallState original entered after input output frame
        (armSmallResult (inputLimb original input) word).1 (inputLimb original input 0 + word)
        (armSmallResult (inputLimb original input) word).2 →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 47
          (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (armSmallArguments input output word) frame [] entered = .ok (final, returned) ∧ post final returned := by
  apply arm_small_ready_prefix enabled original entered input output word frame call setup homes post
  intro current ready
  exact ready.compute enabled (armSmallArguments input output word)
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes post continuation

#print axioms ARMSmallReady.compute
#print axioms arm_small_computed_prefix

#print axioms ARMSmallState.carry
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open UInt256Model.Safety

/-- Execution's explicit limb updates equal the independently proved small sum. -/
theorem arm_small_result_words (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    armSmallOutputWords (armSmallResult words word).1 (words 0 + word) =
      UInt256Proof.smallResult words word := by
  by_cases carry : words 0 + word < words 0 <;>
    by_cases first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
  all_goals
    funext ⟨i, bound⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [armSmallOutputWords, armSmallResult, armCarryResult, armIncrementWord,
        UInt256Proof.smallResult, carry, first, second]

theorem arm_small_result_value (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference)
    (word : BitVec 64) :
    UInt256Model.value (armSmallOutputWords (armSmallResult (inputLimb memory input) word).1
      (inputLimb memory input 0 + word)) = inputValue memory input + BitVec.ofNat 256 word.toNat := by
  rw [arm_small_result_words, UInt256Proof.small_result_sum]
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [initial]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- The returned byte bit is exactly overflow of the mathematical 256-bit sum. -/
theorem arm_small_result_flag (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    (armSmallResult words word).2 =
      if 2^256 ≤ (UInt256Model.value words).toNat + word.toNat then 1 else 0 := by
  have overflow := UInt256Proof.Reporting.small_overflow_iff words word
  have wideBound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
  have single : (UInt256Model.value (UInt256Proof.singleLimb word)).toNat = word.toNat := by
    simp [UInt256Model.value, UInt256Proof.singleLimb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound]
  rw [single] at overflow
  simp only [← overflow]
  by_cases carry : words 0 + word < words 0 <;>
    by_cases first : words 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases second : words 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 <;>
    by_cases third : words 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0
  all_goals
    simp [armSmallResult, armCarryResult, armIncrementWord, carry, first, second, third]

#print axioms arm_small_result_words
#print axioms arm_small_result_value
#print axioms arm_small_result_flag
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

structure ARMSmallPost (original final : Memory) (returned : List Value)
    (input output : Reference) (word : BitVec 64) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original input + BitVec.ofNat 256 word.toNat
  flag : returned = [.scalar (.i32 (if 2^256 ≤ (inputValue original input).toNat + word.toNat then 1 else 0))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Full extracted ARM helper execution satisfies independent addition and exact
    overflow, retiring private storage while preserving every other caller byte. -/
theorem arm_small_entry (enabled : Extracted.profile.advSimd = true)
    (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (armSmallArguments input output word) frame [] entered = .ok (final, returned) ∧
      ARMSmallPost original final returned input output word := by
  let post := fun final returned => ARMSmallPost original final returned input output word
  apply arm_small_computed_prefix enabled original entered input output word frame call setup homes post
  intro current state
  apply state.output enabled (armSmallArguments input output word) (by rfl) call homes post
  intro stored valid outside _ value
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retired := leaveFrame_preserves_memory_below frame stored original.nextIdentity
    (fun id member => (fresh.2 id member).1)
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retired.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have mathematical := value.trans (arm_small_result_value original input word)
    simpa only [inputValue, bytes] using mathematical
  · have initial : UInt256Model.value (inputLimb original input) = inputValue original input :=
      UInt256Proof.input_value (fun offset => (original.cells input.allocation offset).bits) input.offset
    have exactFlag := arm_small_result_flag (inputLimb original input) word
    rw [initial] at exactFlag
    simp only [exactFlag]
  · exact (retired.access output outputOld 32 1 true).trans
      (valid.1.2.2 (wordView output) (by simp))
  · intro id old offset untouched
    exact (retired.cells id old offset).trans
      ((outside id offset untouched).trans (state.preserved.cells id old offset))

#print axioms arm_small_entry
end UInt256Proof.Add.Safety
