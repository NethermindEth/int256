import UInt256.Methods.Add.ARMSmallPrefix

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety
/-- Retain every extracted numeric kind, including the ARM one-byte flag. -/
def armSmallSpecs : List NumericLocalSpec := List.replicate 6 armWordSpec ++ [⟨.narrow .unsigned8, .i32 0, 0, rfl⟩]

theorem arm_small_local_metadata (profile : CIL.FeatureProfile) (storage : Nat) :
    (armSmallBody profile storage).localKinds = numericKinds armSmallSpecs ∧
    (armSmallBody profile storage).locals = numericInitializers armSmallSpecs := by
  constructor <;> rfl

theorem arm_small_frame_setup (profile : CIL.FeatureProfile) (storage : Nat) (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame (armSmallBody profile storage) args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity armSmallSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup (armSmallBody profile storage) armSmallSpecs (arm_small_local_metadata profile storage).1
    (arm_small_local_metadata profile storage).2 (by rfl) (by rfl) (by rfl) memory args wf

/-- Original initialized-home evidence justifies later private writes after any prior checked writes, with byte width and representability checked explicitly. -/
theorem arm_small_private_store (program : CIL.Program) (profile : CIL.FeatureProfile) (storage : Nat) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame)
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary armSmallSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec) (specified : armSmallSpecs[index]? = some spec)
    (value : CIL.Value) (number : Nat) (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 = .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step (armSmallBody profile storage) (.setLocal index) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) :=
  checked_numeric_store program (armSmallBody profile storage) armSmallSpecs boundary
    entered current inputs outputs frame call enteredWF homes authority index spec specified value number fits

#print axioms arm_small_local_metadata
#print axioms arm_small_frame_setup
#print axioms arm_small_private_store
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armSmallWordSpec : NumericLocalSpec := ⟨.word64, .i64 0, 0, rfl⟩

theorem arm_small_input_spec (i : Fin 4) : armSmallSpecs[i.val]? = some armSmallWordSpec := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

structure ARMSmallSaved (program : CIL.Program) (original entered current : Memory)
    (input output : Reference) (frame : Frame) (done : Nat) : Prop where
  call : CallingConditions program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  completed : ∀ i : Fin 4, i.val < done → ∃ reference,
    frame.locals[i.val]? = some (.bytes .word64 reference) ∧
      read current reference 8 1 = .ok (numberBytes (inputLimb original input i).toNat 8)

theorem ARMSmallSaved.save {program : CIL.Program} {profile : CIL.FeatureProfile} {storage : Nat} {original entered current : Memory}
    {input output : Reference} {frame : Frame}
    (index : Fin 4) (state : ARMSmallSaved program original entered current input output frame index.val)
    (word : BitVec 64) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after, ARMSmallSaved program original entered after input output frame (index.val + 1) ∧
      ∀ pc rest, step (armSmallBody profile storage) (.setLocal index.val) pc
        (armSmallArguments input output word) frame
        (.scalar (.i64 (inputLimb original input index)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, authority, written, stepped⟩ :=
    arm_small_private_store program profile storage original.nextIdentity entered current [input] [output] frame
      state.call enteredWF homes state.authority index.val armSmallWordSpec (arm_small_input_spec index)
      (.i64 (inputLimb original input index)) (inputLimb original input index).toNat rfl
  refine ⟨after, ⟨afterCall, state.preserved.trans preserved, authority, ?_⟩,
    fun pc rest => stepped pc _ rest⟩
  intro i saved
  by_cases equal : i = index
  · subst i
    exact ⟨reference, slot, loaded⟩
  · have earlier : i.val < index.val := by
      have different : i.val ≠ index.val := fun h => equal (Fin.ext h)
      omega
    obtain ⟨previous, previousSlot, previousRead⟩ := state.completed i earlier
    have different := Nat.ne_of_lt
      (homes.ordered i.val index.val .word64 .word64 previous reference earlier previousSlot slot)
    exact ⟨previous, previousSlot,
      write_preserves_disjoint_read written previousRead (Or.inl different)⟩

theorem arm_small_input_prefix_checked (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true) (original entered : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (armSmallBody profile storage) (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after, ARMSmallSaved program original entered after input output frame 4 →
      ∃ fuel result returned,
        run program fuel method 14
          (armSmallArguments input output word) frame [] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method 0
        (armSmallArguments input output word) frame [] entered = .ok (result, returned) ∧
      post result returned := by
  have enteredCall := call.after_frame_setup setup
  have initial : ARMSmallSaved program original entered entered input output frame 0 :=
    ⟨enteredCall, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow, by intro i impossible; omega⟩
  obtain ⟨first, saved1, step0⟩ := initial.save (profile := profile) (storage := storage) 0 word enteredCall.1.1 homes
  obtain ⟨second, saved2, step1⟩ := saved1.save (profile := profile) (storage := storage) 1 word enteredCall.1.1 homes
  obtain ⟨third, saved3, step2⟩ := saved2.save (profile := profile) (storage := storage) 2 word enteredCall.1.1 homes
  obtain ⟨fourth, saved4, step3⟩ := saved3.save (profile := profile) (storage := storage) 3 word enteredCall.1.1 homes
  let states : Nat → CIL.Safety.Memory := fun n => match n with
    | 0 => entered | 1 => first | 2 => second | 3 => third | _ => fourth
  have saved : ∀ i : Fin 4, ARMSmallSaved program original entered (states i.val) input output frame i.val := by
    intro ⟨i, bound⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact initial
    · exact saved1
    · exact saved2
    · exact saved3
  apply arm_small_input_prefix program method storage profile found enabled input output word (inputLimb original input) frame states
    (fun i => (saved i).call.input_formed (by simp)) ?_ ?_ post
    (continuation fourth saved4)
  · intro i rest
    rw [(saved i).call.input_field_instruction (by simp) i rest]
    simp only [inputLimb,
      call.input_bytes_of_memory_below (saved i).preserved (reference := input) (by simp)]
  · intro ⟨i, bound⟩ pc rest
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact step0 pc rest
    · exact step1 pc rest
    · exact step2 pc rest
    · exact step3 pc rest

/-- Later sum/flag homes cannot overwrite any of the four saved input limbs. -/
theorem ARMSmallSaved.after_later_write {program : CIL.Program} {original entered current after : Memory}
    {input output : Reference} {frame : Frame} {done index : Nat}
    {kind : CIL.LocalKind} {reference : Reference} {bytes : List (BitVec 8)}
    (state : ARMSmallSaved program original entered current input output frame done)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (later : 4 ≤ index) (slot : frame.locals[index]? = some (.bytes kind reference))
    (written : write current reference bytes 1 = .ok after)
    (preserved : MemoryBelow original.nextIdentity current after) :
    ARMSmallSaved program original entered after input output frame done := by
  refine ⟨state.call.after_write written, state.preserved.trans preserved,
    state.authority.trans (write_preserves_access_below written _), ?_⟩
  intro i completed
  obtain ⟨home, homeSlot, loaded⟩ := state.completed i completed
  have separate := Nat.ne_of_lt
    (homes.ordered i.val index .word64 kind home reference (by omega) homeSlot slot)
  exact ⟨home, homeSlot, write_preserves_disjoint_read written loaded (Or.inl separate)⟩

#print axioms ARMSmallSaved.after_later_write

#print axioms arm_small_input_prefix_checked
#print axioms arm_small_input_spec
#print axioms ARMSmallSaved.save
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

structure ARMSmallReady (program : CIL.Program) (original entered current : Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame) : Prop where
  saved : ARMSmallSaved program original entered current input output frame 4
  sum : ∃ home, frame.locals[5]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes (inputLimb original input 0 + word).toNat 8)
  flag : ∃ home, frame.locals[6]? = some (.bytes (.narrow .unsigned8) home) ∧
    read current home 1 1 = .ok (numberBytes 0 1)

/-- Derive both private stores and preserve all initial input snapshots before the first carry decision. -/
theorem arm_small_prepare (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (original entered current : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (saved : ARMSmallSaved program original entered current input output frame 4)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, ARMSmallReady program original entered after input output word frame →
      ∃ fuel final returned,
        run program fuel method 20
          (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 14
        (armSmallArguments input output word) frame [] current = .ok (final, returned) ∧ post final returned := by
    obtain ⟨lowHome, lowSlot, lowRead⟩ := saved.completed 0 (by decide)
    obtain ⟨sumHome, middle, sumSlot, sumRead, sumPreserved, _, _, sumWritten, sumStep⟩ :=
      arm_small_private_store program profile storage original.nextIdentity entered current [input] [output] frame
        saved.call enteredWF homes saved.authority 5 armSmallWordSpec (by rfl)
        (.i64 (inputLimb original input 0 + word)) (inputLimb original input 0 + word).toNat rfl
    have middleSaved := saved.after_later_write homes (by decide : 4 ≤ 5) sumSlot sumWritten sumPreserved
    obtain ⟨flagHome, after, flagSlot, flagRead, flagPreserved, _, _, flagWritten, flagStep⟩ :=
      arm_small_private_store program profile storage original.nextIdentity entered middle [input] [output] frame
        middleSaved.call enteredWF homes middleSaved.authority 6 ⟨(.narrow .unsigned8), .i32 0, 0, rfl⟩ (by rfl)
        (.i32 0) 0 rfl
    have afterSaved := middleSaved.after_later_write homes (by decide : 4 ≤ 6) flagSlot flagWritten flagPreserved
    have separate := Nat.ne_of_lt
      (homes.ordered 5 6 .word64 (.narrow .unsigned8) sumHome flagHome (by decide) sumSlot flagSlot)
    have sumAfter := write_preserves_disjoint_read flagWritten sumRead (Or.inl separate)
    have ready : ARMSmallReady program original entered after input output word frame :=
      ⟨afterSaved, ⟨sumHome, sumSlot, sumAfter⟩, ⟨flagHome, flagSlot, flagRead⟩⟩
    apply arm_small_sum program method storage profile found enabled input output lowHome word (inputLimb original input 0) frame
      current middle lowSlot lowRead (sumStep 17 _ []) post
    apply run_next_exists post found (by rfl)
    · simp [step, cil_guard, observerCount, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · exact run_next_exists (op := .setLocal 6 (some .unsigned8)) post found (by rfl) (flagStep 19 (armSmallArguments input output word) []) (continuation after ready)

/-- Connect actual helper entry to a fully initialized carry-decision state. -/
theorem arm_small_ready_prefix (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    (original entered : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (setup : enterFrame (armSmallBody profile storage) (armSmallArguments input output word) original =
      .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, ARMSmallReady program original entered after input output word frame →
      ∃ fuel final returned,
        run program fuel method 20
          (armSmallArguments input output word) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 0
        (armSmallArguments input output word) frame [] entered = .ok (final, returned) ∧ post final returned := by
  apply arm_small_input_prefix_checked program method storage profile found enabled original entered input output word frame call setup homes post
  intro current saved
  exact arm_small_prepare program method storage profile found enabled original entered current input output word frame
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes saved post continuation

#print axioms arm_small_prepare
#print axioms arm_small_ready_prefix
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety
theorem arm_small_store_return (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (enabled : profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (inputs : List Reference)
    (output flagHome : Reference) (words : Fin 4 → BitVec 64) (flag : BitVec 32)
    (call : CallingConditions program memory inputs [output])
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (fits : localNumber (.narrow .unsigned8) (.i32 flag) = .ok flag.toNat)
    (flagSlot : frame.locals[6]? = some (.bytes (.narrow .unsigned8) flagHome))
    (flagRead : read memory flagHome 1 1 = .ok (numberBytes flag.toNat 1))
    (flagOld : flagHome.allocation < memory.nextIdentity)
    (privateFlag : flagHome.allocation ≠ output.allocation)
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored,
      CallingConditions program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = memory.cells id offset) →
      AccessBelow memory.nextIdentity memory stored →
      inputValue stored output = UInt256Model.value words →
      post (leaveFrame frame stored) [.scalar (.i32 flag)]) :
    ∃ fuel final returned,
      run program fuel method 52 args frame
        [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory =
            .ok (final, returned) ∧ post final returned := by
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, readable⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract profile program storage storageFound
      memory inputs output (words 0) (words 1) (words 2) (words 3) call
  have formed := call.output_formed (by simp : output ∈ [output])
  have stepped : step (armSmallBody profile storage) (.call storage 5) 52 args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] memory =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3)) [] memory) := by
    simp [step, cil_guard, observerCount, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  have retained : read stored flagHome 1 1 = .ok (numberBytes flag.toNat 1) := by
    apply authority.read_eq flagRead flagOld
    intro i bound
    exact outside _ _ (Or.inl privateFlag)
  have returned := arm_small_return program method storage profile found enabled stored frame args flagHome flag
    flagFit fits flagSlot retained
  obtain ⟨fuel, executed⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨2, returned⟩
  refine ⟨fuel, leaveFrame frame stored, [.scalar (.i32 flag)], executed, ?_⟩
  apply continuation stored valid outside authority
  simpa only [UInt256Model.value] using value
#print axioms arm_small_store_return
end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Distinct extracted numeric slots have distinct allocation identities. -/
theorem arm_small_other_read {entered before after : Memory} {boundary : Nat}
    {slots : List LocalSlot} (homes : NumericHomes entered boundary armSmallSpecs slots)
    {i j : Nat} (different : i ≠ j) {source target : Reference}
    {sourceKind targetKind : CIL.LocalKind}
    (sourceSlot : slots[i]? = some (.bytes sourceKind source))
    (targetSlot : slots[j]? = some (.bytes targetKind target))
    {bytes value : List (BitVec 8)} {width : Nat}
    (written : write before target bytes 1 = .ok after)
    (loaded : read before source width 1 = .ok value) :
    read after source width 1 = .ok value := by
  by_cases earlier : i < j
  · exact write_preserves_disjoint_read written loaded
      (Or.inl (Nat.ne_of_lt (homes.ordered i j sourceKind targetKind source target earlier sourceSlot targetSlot)))
  · exact write_preserves_disjoint_read written loaded
      (Or.inl (Nat.ne_of_gt (homes.ordered j i targetKind sourceKind target source (by omega) targetSlot sourceSlot)))

structure ARMSmallState (program : CIL.Program) (original entered current : Memory) (input output : Reference)
    (frame : Frame) (words : Fin 4 → BitVec 64) (sum : BitVec 64) (flag : BitVec 32) : Prop where
  call : CallingConditions program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  limbs : ∀ i : Fin 4, ∃ home, frame.locals[i.val]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes (words i).toNat 8)
  sumRead : ∃ home, frame.locals[5]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes sum.toNat 8)
  flagRead : ∃ home, frame.locals[6]? = some (.bytes (.narrow .unsigned8) home) ∧
    read current home 1 1 = .ok (numberBytes flag.toNat 1)
  flagRoundtrip : CIL.NarrowKind.unsigned8.extend flag = flag
  flagFits : localNumber (.narrow .unsigned8) (.i32 flag) = .ok flag.toNat

theorem ARMSmallReady.state {program : CIL.Program} {original entered current : Memory} {input output : Reference}
    {word : BitVec 64} {frame : Frame}
    (ready : ARMSmallReady program original entered current input output word frame) :
    ARMSmallState program original entered current input output frame (inputLimb original input)
      (inputLimb original input 0 + word) 0 :=
  ⟨ready.saved.call, ready.saved.preserved, ready.saved.authority,
    fun i => ready.saved.completed i i.isLt, ready.sum, ready.flag, rfl, rfl⟩

/-- Updating one saved limb derives the actual store and preserves all remaining initialized homes, including the low sum and the one-byte flag. -/
theorem ARMSmallState.store_limb {program : CIL.Program} {profile : CIL.FeatureProfile} {storage : Nat} {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState program original entered current input output frame words sum flag)
    (index : Fin 4) (value : BitVec 64) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after,
      ARMSmallState program original entered after input output frame
        (fun i => if i = index then value else words i) sum flag ∧
      ∀ pc args rest, step (armSmallBody profile storage) (.setLocal index.val) pc args frame
        (.scalar (.i64 value) :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨home, after, slot, loaded, preserved, call, authority, written, stepped⟩ :=
    arm_small_private_store program profile storage original.nextIdentity entered current [input] [output] frame
      state.call enteredWF homes state.authority index.val armSmallWordSpec (arm_small_input_spec index)
      (.i64 value) value.toNat rfl
  refine ⟨after, ⟨call, state.preserved.trans preserved, authority, ?_, ?_, ?_, state.flagRoundtrip, state.flagFits⟩, stepped⟩
  · intro i
    by_cases same : i = index
    · subst i
      exact ⟨home, slot, by simpa [armSmallWordSpec, localWidth] using loaded⟩
    · obtain ⟨other, otherSlot, otherRead⟩ := state.limbs i
      refine ⟨other, otherSlot, ?_⟩
      simp only [same, ite_false]
      exact arm_small_other_read homes (fun h => same (Fin.ext h)) otherSlot slot written otherRead
  · obtain ⟨other, otherSlot, otherRead⟩ := state.sumRead
    exact ⟨other, otherSlot, arm_small_other_read homes (by omega) otherSlot slot written otherRead⟩
  · obtain ⟨other, otherSlot, otherRead⟩ := state.flagRead
    exact ⟨other, otherSlot, arm_small_other_read homes (by omega) otherSlot slot written otherRead⟩

/-- Updating the byte flag preserves all limb and sum snapshots. -/
theorem ARMSmallState.store_flag (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState program original entered current input output frame words sum flag)
    (value : BitVec 32) (valueFit : CIL.NarrowKind.unsigned8.extend value = value) (fits : localNumber (.narrow .unsigned8) (.i32 value) = .ok value.toNat)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after, ARMSmallState program original entered after input output frame words sum value ∧
      ∀ pc args rest, step (armSmallBody profile storage) (.setLocal 6) pc args frame
        (.scalar (.i32 value) :: rest) current = .ok (.next (pc + 1) rest frame after) := by
    obtain ⟨home, after, slot, loaded, preserved, call, authority, written, stepped⟩ :=
      arm_small_private_store program profile storage original.nextIdentity entered current [input] [output] frame
        state.call enteredWF homes state.authority 6 ⟨(.narrow .unsigned8), .i32 0, 0, rfl⟩ (by rfl)
        (.i32 value) value.toNat fits
    refine ⟨after, ⟨call, state.preserved.trans preserved, authority, ?_, ?_,
      ⟨home, slot, loaded⟩, valueFit, fits⟩, stepped⟩
    · intro i
      obtain ⟨other, otherSlot, otherRead⟩ := state.limbs i
      exact ⟨other, otherSlot, arm_small_other_read homes (by omega) otherSlot slot written otherRead⟩
    · obtain ⟨other, otherSlot, otherRead⟩ := state.sumRead
      exact ⟨other, otherSlot, arm_small_other_read homes (by decide : 5 ≠ 6) otherSlot slot written otherRead⟩

/-- Execute one carry increment with every memory premise derived from the state. -/
theorem ARMSmallState.increment (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState program original entered current input output frame words sum flag)
    (segment : Fin 3) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ARMSmallState program original entered after input output frame
        (fun i => if i = (⟨segment.val + 1, by omega⟩ : Fin 4)
          then words ⟨segment.val + 1, by omega⟩ + 1 else words i) sum flag →
      ∃ fuel final returned,
        run program fuel method (29 + 7 * segment.val) args frame
          [.scalar (.i64 (words ⟨segment.val + 1, by omega⟩ + 1))] after =
            .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (23 + 7 * segment.val) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  obtain ⟨home, slot, loaded⟩ := state.limbs index
  obtain ⟨after, updated, stored⟩ := state.store_limb (profile := profile) (storage := storage) index (words index + 1) enteredWF homes
  exact arm_small_increment program method storage profile found enabled segment current after frame args home (words index) slot loaded
    (fun pc rest => stored pc args rest) post (continuation after updated)

#print axioms ARMSmallState.store_flag
#print axioms ARMSmallState.increment

#print axioms arm_small_other_read
#print axioms ARMSmallReady.state
#print axioms ARMSmallState.store_limb
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armSmallOutputWords (words : Fin 4 → BitVec 64) (sum : BitVec 64) : Fin 4 → BitVec 64 :=
  fun i => if i.val = 0 then sum else words i

theorem ARMSmallState.final_flag (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    {original entered current : Memory} {input output : Reference} {frame : Frame}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState program original entered current input output frame words sum flag)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ARMSmallState program original entered after input output frame words sum
        (if words 3 = BitVec.ofNat 64 0 then 1 else 0) →
      ∃ fuel final returned,
        run program fuel method 47 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 43 args frame [.scalar (.i64 (words 3))] current =
        .ok (final, returned) ∧ post final returned := by
  let bit : BitVec 32 := if words 3 = BitVec.ofNat 64 0 then 1 else 0
  have fits : localNumber (.narrow .unsigned8) (.i32 bit) = .ok bit.toNat := by
    dsimp only [bit]
    split <;> rfl
  obtain ⟨after, updated, stored⟩ := state.store_flag program method storage profile found enabled bit (by dsimp [bit]; split <;> rfl) fits enteredWF homes
  exact arm_small_final_flag program method storage profile found enabled current after frame args (words 3) (stored 46 args [])
    post (continuation after updated)

/-- Every output argument and the flag read are derived from the carry state. -/
theorem ARMSmallState.output (program : CIL.Program) (method storage : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage)) (enabled : profile.advSimd = true)
    {original entered current : Memory} {input output : Reference} {frame : Frame}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) (state : ARMSmallState program original entered current input output frame words sum flag)
    (args : List Value) (argument : args[2]? = some (.reference (.address output)))
    (originalCall : CallingConditions program original [input] [output])
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored,
      CallingConditions program stored [input] [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = current.cells id offset) →
      AccessBelow current.nextIdentity current stored →
      inputValue stored output = UInt256Model.value (armSmallOutputWords words sum) →
      post (leaveFrame frame stored) [.scalar (.i32 flag)]) :
    ∃ fuel final returned,
      run program fuel method 47 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  classical
  have candidates : ∀ i : Fin 4, ∃ home,
      frame.locals[if i.val = 0 then 5 else i.val]? = some (.bytes .word64 home) ∧
      read current home 8 1 = .ok (numberBytes (armSmallOutputWords words sum i).toNat 8) := by
    intro i
    by_cases zero : i.val = 0
    · simpa only [armSmallOutputWords, zero, ite_true] using state.sumRead
    · simpa only [armSmallOutputWords, zero, ite_false] using state.limbs i
  let outputHomes := fun i => Classical.choose (candidates i)
  have facts := fun i => Classical.choose_spec (candidates i)
  apply arm_small_output_arguments program method storage profile found enabled current frame args output outputHomes
    (armSmallOutputWords words sum) (fun i => (facts i).1) (fun i => (facts i).2)
    argument (state.call.output_formed (by simp)) post
  obtain ⟨flagHome, flagSlot, flagRead⟩ := state.flagRead
  have fresh := homes.home_bound 6 (.narrow .unsigned8) flagHome flagSlot
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (read_reference_valid _ _ _ _ _ flagRead)
  have flagOld := (state.call.1.1.1 _ _ present).1
  obtain ⟨outAllocation, outPresent, _, _⟩ := formed_reference_live _ _ _
    (originalCall.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (originalCall.1.1.1 _ _ outPresent).1
  exact arm_small_store_return program method storage profile found storageFound enabled current frame args [input] output flagHome
    (armSmallOutputWords words sum) flag state.call state.flagRoundtrip state.flagFits flagSlot flagRead flagOld
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le outputOld fresh)) post continuation

#print axioms ARMSmallState.final_flag
#print axioms ARMSmallState.output
end UInt256Proof.Add.Safety
