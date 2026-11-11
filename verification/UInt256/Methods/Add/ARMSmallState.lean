import UInt256.Methods.Add.ARMSmallPrefix
import CIL.Safety.LocalSnapshots

/-! Small-addition states retain caller guarantees and shared numeric-local snapshots. -/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Actual initialized homes, including the one-byte ARM flag. -/
def armSmallSpecs : List NumericLocalSpec :=
  List.replicate 6 armWordSpec ++ [⟨.narrow .unsigned8, .i32 0, 0, rfl⟩]

/-- Entry allocates numeric homes without changing caller memory. -/
theorem arm_small_frame_setup (profile : CIL.FeatureProfile) (storage : Nat)
    (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame (armSmallBody profile storage) args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity armSmallSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup (armSmallBody profile storage) armSmallSpecs
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) memory args wf

/-- Snapshot values of the input limbs saved so far. -/
def smallSaved (words : Fin 4 → BitVec 64) (done : Nat) : Nat → Option CIL.Value :=
  fun index => if bound : index < 4 then
    if index < done then some (.i64 (words ⟨index, bound⟩)) else none else none

/-- ARM uses local5 for the low sum and local6 for the byte flag. -/
def armSmallKnown (words : Fin 4 → BitVec 64) (sum : BitVec 64) (flag : BitVec 32) :=
  rememberLocal (rememberLocal (smallSaved words 4) 5 (.i64 sum)) 6 (.i32 flag)

/-- Updating a saved limb leaves the low-sum and byte-flag slots unchanged. -/
theorem armSmallKnown_store_word (words : Fin 4 → BitVec 64) (sum : BitVec 64)
    (flag : BitVec 32) (index : Nat) (bound : index < 4) (value : BitVec 64) :
    rememberLocal (armSmallKnown words sum flag) index (.i64 value) =
      armSmallKnown (fun i => if i.val = index then value else words i) sum flag := by
  funext other
  by_cases same : other = index
  · subst other
    simp [armSmallKnown, rememberLocal, smallSaved, bound,
      show index ≠ 5 by omega, show index ≠ 6 by omega]
  · by_cases below : other < 4 <;>
      simp [armSmallKnown, rememberLocal, smallSaved, same, below]

/-- Replacing the byte flag retains all saved limbs and the low sum. -/
theorem armSmallKnown_store_flag (words : Fin 4 → BitVec 64) (sum : BitVec 64)
    (flag value : BitVec 32) :
    rememberLocal (armSmallKnown words sum flag) 6 (.i32 value) =
      armSmallKnown words sum value := by
  funext index
  by_cases same : index = 6 <;> simp [armSmallKnown, rememberLocal, same]
/-- Caller guarantees and exact loaded values of private numeric locals. -/
structure SmallState (program : CIL.Program) (original entered current : Memory)
    (input output : Reference) (frame : Frame) (known : Nat → Option CIL.Value) : Prop where
  call : CallingConditions program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  snapshots : LocalSnapshots current frame.locals known

/-- Saved inputs remain independent of subsequent output aliasing. -/
abbrev ARMSmallSaved (program : CIL.Program) (original entered current : Memory)
    (input output : Reference) (frame : Frame) (done : Nat) :=
  SmallState program original entered current input output frame
    (smallSaved (inputLimb original input) done)

/-- A checked private store updates one shared snapshot and preserves caller guarantees. -/
theorem SmallState.store {program : CIL.Program} {original entered current : Memory}
    {input output : Reference} {frame : Frame} {known : Nat → Option CIL.Value}
    (state : SmallState program original entered current input output frame known)
    (body : CIL.Method) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (index : Nat) (spec : NumericLocalSpec) (specified : armSmallSpecs[index]? = some spec)
    (value : CIL.Value) (number : Nat) (fits : localNumber spec.kind value = .ok number) :
    ∃ after, SmallState program original entered after input output frame
        (rememberLocal known index (localResult spec.kind value)) ∧
      ∀ pc args rest, step body (.setLocal index) pc args frame (.scalar value :: rest) current =
        .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨home, after, slot, _, preserved, call, authority, written, stepped⟩ :=
    checked_numeric_store program body armSmallSpecs original.nextIdentity entered current
      [input] [output] frame state.call enteredWF homes state.authority
      index spec specified value number fits
  exact ⟨after, ⟨call, state.preserved.trans preserved, authority,
    state.snapshots.after_write homes.writable index spec.kind home value number fits slot written⟩,
    stepped⟩

/-- Saving the next input extends the remembered prefix by exactly one limb. -/
theorem SmallState.save {program : CIL.Program} {original entered current : Memory}
    {input output : Reference} {frame : Frame} (index : Fin 4)
    (state : ARMSmallSaved program original entered current input output frame index.val)
    (body : CIL.Method) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after, ARMSmallSaved program original entered after input output frame (index.val + 1) ∧
      ∀ pc args rest, step body (.setLocal index.val) pc args frame
        (.scalar (.i64 (inputLimb original input index)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  have specified : armSmallSpecs[index.val]? = some armWordSpec := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨after, saved, stepped⟩ := state.store body enteredWF homes index.val armWordSpec
    specified (.i64 (inputLimb original input index)) (inputLimb original input index).toNat rfl
  have maps : rememberLocal (smallSaved (inputLimb original input) index.val) index.val
      (localResult armWordSpec.kind (.i64 (inputLimb original input index))) =
      smallSaved (inputLimb original input) (index.val + 1) := by
    funext other
    by_cases same : other = index.val
    · subst other
      simp [rememberLocal, smallSaved, index.isLt, armWordSpec, localResult]
    · by_cases bound : other < 4
      · have next : (other < index.val + 1) = (other < index.val) := propext (by omega)
        simp [rememberLocal, smallSaved, same, bound, next]
      · simp [rememberLocal, smallSaved, same, bound]
  rw [maps] at saved
  exact ⟨after, saved, stepped⟩
/-- The output replaces the saved low input with its computed sum. -/
def armSmallOutputWords (words : Fin 4 → BitVec 64) (sum : BitVec 64) : Fin 4 → BitVec 64 :=
  fun index => if index.val = 0 then sum else words index

/-- Store result limbs, retain the private flag snapshot and return it checked. -/
theorem arm_small_store_return (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (armSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (memory entered : Memory) (boundary : Nat) (frame : Frame) (args : List Value)
    (inputs : List Reference) (output : Reference) (words : Fin 4 → BitVec 64)
    (flag : BitVec 32) (known : Nat → Option CIL.Value)
    (call : CallingConditions program memory inputs [output])
    (homes : NumericHomes entered boundary armSmallSpecs frame.locals)
    (snapshots : LocalSnapshots memory frame.locals known) (flagKnown : known 6 = some (.i32 flag))
    (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (outputOld : output.allocation < boundary)
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored, CallingConditions program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset →
        stored.cells id offset = memory.cells id offset) →
      AccessBelow memory.nextIdentity memory stored →
      inputValue stored output = UInt256Model.value words →
      post (leaveFrame frame stored) [.scalar (.i32 flag)]) :
    WP (Execution (fun fuel => run program fuel method 52 args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] memory))
      (Function.uncurry post) := by
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract
      profile program storage storageFound
      memory inputs output (words 0) (words 1) (words 2) (words 3) call
  have formed := call.output_formed (by simp : output ∈ [output])
  have stepped : step (armSmallBody profile storage) (.call storage 5) 52 args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] memory =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output
        (words 0) (words 1) (words 2) (words 3)) [] memory) := by
    cil_checked_step [UInt256Proof.Multiply.LimbStorage.arguments, formed]
  have retained := snapshots.after_unchanged call.1.1 authority (by
    intro index loaded kind home _ slot offset _
    exact outside _ _ (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le outputOld
      (homes.home_bound index kind home slot)))))
  have loaded := retained.load (body := armSmallBody profile storage) (args := args)
    (stack := []) (pc := 53) (.i32 flag) flagKnown
  have suffix : WP (Execution (fun fuel => run program fuel method 53 args frame [] stored))
      (Function.uncurry post) := by
    cil_contract_steps [found, loaded, flagFit]

    exact continuation stored valid outside authority
      (by simpa only [UInt256Model.value] using value)
  apply WP.call (helperPost := fun result => result.1 = stored ∧ result.2 = [])
    found (by rfl) stepped ⟨childFuel, (stored, []), invoked, rfl, rfl⟩
  rintro final values ⟨rfl, rfl⟩
  exact suffix
end UInt256Proof.Add.Safety
