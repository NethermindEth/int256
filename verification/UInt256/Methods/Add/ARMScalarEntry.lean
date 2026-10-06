import UInt256.Methods.Add.Vector128ARMScalarSwap
import UInt256.Methods.Add.ARMSmallParentCall
import UInt256.Methods.Add.ScalarReportingResult

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

theorem arm_scalar_small_value (memory : Memory) (input : Reference)
    (small : armScalarUpper memory input = BitVec.ofNat 64 0) :
    inputValue memory input = BitVec.ofNat 256 (inputLimb memory input 0).toNat := by
  obtain ⟨upper, h3⟩ := BitVec.or_eq_zero_iff.mp small
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp upper
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [← initial, ← UInt256Proof.singleLimb_eq (inputLimb memory input) h1 h2 h3]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- Convert either selected small operand into the same initial two-input sum,
    including its unbounded natural sum for the exact overflow contract. -/
theorem arm_scalar_small_values (swapped : Bool) (original current : Memory)
    (left right output : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (small : armScalarUpper current (if swapped then left else right) = BitVec.ofNat 64 0) :
    let word := inputLimb current (if swapped then left else right) 0
    (inputValue current (if swapped then right else left) + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right) ∧
    ((inputValue current (if swapped then right else left)).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) := by
  have smallValue := arm_scalar_small_value current (if swapped then left else right) small
  have wideBound : (inputLimb current (if swapped then left else right) 0).toNat < 2^256 :=
    Nat.lt_trans (inputLimb current (if swapped then left else right) 0).isLt (by decide)
  have kept : ∀ reference ∈ [left, right], inputValue current reference = inputValue original reference := by
    intro reference member
    simp only [inputValue, call.input_bytes_of_memory_below preserved member]
  have keptLeft := kept left (by simp)
  have keptRight := kept right (by simp)
  cases swapped
  · dsimp at smallValue wideBound ⊢
    rw [← keptLeft, ← keptRight, smallValue]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound]
  · dsimp at smallValue wideBound ⊢
    rw [← keptLeft, ← keptRight, smallValue]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound, BitVec.add_comm, Nat.add_comm]

/-- Select one existing readable input view without imposing alias restrictions. -/
theorem arm_scalar_select_input (memory : Memory) (inputs : List Reference) (input output : Reference)
    (call : CallingConditions Extracted.program memory inputs [output]) (member : input ∈ inputs) :
    CallingConditions Extracted.program memory [input] [output] := by
  refine ⟨⟨call.1.1, ?_, call.1.2.2⟩, call.2⟩
  intro view selected
  have same : view = wordView input := by simpa using selected
  subst view
  exact call.1.2.1 _ (List.mem_map.mpr ⟨input, member, rfl⟩)

/-- Original frame-home authority bounds the current allocation watermark. -/
theorem arm_scalar_watermark (original entered current : Memory) (frame : Frame)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (enteredWF : entered.WellFormed) (currentWF : current.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) :
    original.nextIdentity ≤ current.nextIdentity := by
  obtain ⟨home, _, fresh, _, writable⟩ := homes.word_at 0 0 (by rfl)
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have retained := authority.access writable (enteredWF.1 _ _ ready.present).1
  obtain ⟨currentAllocation, currentReady⟩ := access_requirements retained
  exact Nat.le_trans fresh (Nat.le_of_lt (currentWF.1 _ _ currentReady.present).1)

#print axioms arm_scalar_small_value
#print axioms arm_scalar_small_values
#print axioms arm_scalar_select_input
#print axioms arm_scalar_watermark
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Complete the small route from its saved arguments, certified helper call,
    scalar forwarding return and parent retirement. -/
theorem arm_scalar_small_finish (enabled : Extracted.profile.advSimd = true)
    (original current : Memory) (frame : Frame) (args : List Value)
    (left right output source home : Reference) (word : BitVec 64) (flag : BitVec 32)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [source] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (root : frame.locals[7]? = some (.root (some (.address source))))
    (slot : frame.locals[8]? = some (.bytes .word64 home))
    (loaded : read current home 8 1 = .ok (numberBytes word.toNat 8))
    (outputArg : args[2]? = some (.reference (.address output)))
    (sum : inputValue current source + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right)
    (naturalSum : (inputValue current source).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 36 args frame [] current = .ok (final, returned) ∧
      ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  apply arm_scalar_small_arguments enabled current frame args source output home word root slot loaded
    (currentCall.input_formed (by simp)) outputArg (currentCall.output_formed (by simp)) post
  apply arm_small_parent_call enabled current source output word frame args currentCall post
  intro childFuel final returned certified result
  refine ⟨arm_scalar_retire original current final frame left right output returned call preserved next owned
    result.wellFormed (result.value.trans sum) ⟨_, result.flag⟩ result.writable result.footprint, ?_⟩
  intro _
  simpa only [naturalSum] using result.flag


/-- The vector route yields the same wrapping postcondition after parent retirement. -/
theorem arm_scalar_vector_finish (enabled : Extracted.profile.advSimd = true)
    (original current : Memory) (frame : Frame) (left right output : Reference) (flag : BitVec 32)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 25 (vector128Arguments left right output flag)
        frame [] current = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  apply vector128_arm_parent_call enabled current left right output flag frame currentCall post
  intro childFuel final returnedFlag certified result overflow writable footprint
  have wellFormed := invoke_preserves_wellFormed _ _ _ _ _ _ _ currentCall.1.1 certified.1
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  rw [keptLeft, keptRight] at result
  refine ⟨arm_scalar_retire original current final frame left right output [.scalar (.i32 returnedFlag)]
    call preserved next owned wellFormed result ⟨returnedFlag, rfl⟩ writable
    (fun id old offset untouched => footprint id offset old untouched), ?_⟩
  intro reporting
  have exactFlag := overflow reporting
  rw [keptLeft, keptRight] at exactFlag
  rw [exactFlag]

#print axioms arm_scalar_vector_finish

#print axioms arm_scalar_retire
#print axioms arm_scalar_small_finish
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- Complete ARM scalar dispatcher execution, including both small-operand routes
    and the vector route. The initial operands may overlap output arbitrarily. -/
theorem arm_scalar_entry (enabled : Extracted.profile.advSimd = true)
    (original entered : Memory) (left right output : Reference) (flag : BitVec 32) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (vector128Arguments left right output flag) original =
      .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 0 (vector128Arguments left right output flag)
        frame [] entered = .ok (final, returned) ∧ ARMScalarReportingPost original final returned left right output flag := by
  let args := vector128Arguments left right output flag
  let post := fun final returned => ARMScalarReportingPost original final returned left right output flag
  have enteredCall := call.after_frame_setup setup
  have setupPreserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have enteredWF := enteredCall.1.1
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ source id, id ∈ (armScalarSavedFrame frame source).owned → original.nextIdentity ≤ id :=
    fun _ id member => (fresh.2 id member).1
  have rootSlot := (arm_scalar_slots enabled entered original.nextIdentity frame homes).1
  have root : ∀ source, (armScalarSavedFrame frame source).locals[7]? =
      some (.root (some (.address source))) := by
    intro source
    simp only [armScalarSavedFrame, List.getElem?_set_self', rootSlot]
    rfl
  have wordSlot : ∀ source home, frame.locals[8]? = some (.bytes .word64 home) →
      (armScalarSavedFrame frame source).locals[8]? = some (.bytes .word64 home) := by
    intro source home slot
    simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot
  apply arm_scalar_dispatch_prefix enabled original.nextIdentity entered [left, right] [output]
    frame args left right enteredCall enteredWF homes (by simp) (by simp) rfl rfl post
  intro home current slot loaded preserved currentCall authority
  have originalPreserved := setupPreserved.trans preserved
  have next := arm_scalar_watermark original entered current frame homes enteredWF currentCall.1.1 authority
  by_cases rightSmall : armScalarUpper current right = BitVec.ofNat 64 0
  · simp only [armScalarTarget, rightSmall, ite_true]
    have lowKept : inputLimb entered right 0 = inputLimb current right 0 := by
      simp only [inputLimb,
        call.input_bytes_of_memory_below setupPreserved (reference := right) (by simp),
        call.input_bytes_of_memory_below originalPreserved (reference := right) (by simp)]
    rw [lowKept] at loaded
    exact arm_scalar_small_finish enabled original current (armScalarSavedFrame frame left) args
      left right output left home (inputLimb current right 0) flag call
      (arm_scalar_select_input current [left, right] left output currentCall (by simp))
      originalPreserved next (owned left) (root left) (wordSlot left home slot) loaded rfl
      (arm_scalar_small_values false original current left right output call originalPreserved rightSmall).1
      (arm_scalar_small_values false original current left right output call originalPreserved rightSmall).2
  · by_cases leftSmall : armScalarUpper current left = BitVec.ofNat 64 0
    · simp only [armScalarTarget, rightSmall, leftSmall, ite_false, ite_true]
      apply arm_scalar_swap_prefix enabled original.nextIdentity entered current [left, right] [output]
        frame args left right currentCall enteredWF homes authority (by simp) (by simp) rfl rfl post
      intro swappedHome after swappedSlot swappedRead afterPreserved afterCall afterAuthority
      have allPreserved := originalPreserved.trans afterPreserved
      have afterNext := arm_scalar_watermark original entered after frame homes enteredWF afterCall.1.1 afterAuthority
      have rightKept : inputValue after right = inputValue current right := by
        simp only [inputValue,
          call.input_bytes_of_memory_below allPreserved (reference := right) (by simp),
          call.input_bytes_of_memory_below originalPreserved (reference := right) (by simp)]
      have sums := arm_scalar_small_values true original current left right output call originalPreserved leftSmall
      apply arm_scalar_small_finish enabled original after (armScalarSavedFrame frame right) args
        left right output right swappedHome (inputLimb current left 0) flag call
        (arm_scalar_select_input after [left, right] right output afterCall (by simp))
        allPreserved afterNext (owned right) (root right) (wordSlot right swappedHome swappedSlot) swappedRead rfl
      · simpa only [rightKept, ite_true] using sums.1
      · simpa only [rightKept, ite_true] using sums.2
    · simp only [armScalarTarget, rightSmall, leftSmall, ite_false]
      exact arm_scalar_vector_finish enabled original current (armScalarSavedFrame frame left)
        left right output flag call currentCall originalPreserved next (owned left)

#print axioms arm_scalar_entry
end UInt256Proof.Add.Safety
