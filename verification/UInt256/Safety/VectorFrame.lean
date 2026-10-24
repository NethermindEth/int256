import CIL.Safety.Equations
import CIL.Safety.WordSnapshots
import CIL.Safety.NumericHomes
import UInt256.Safety.CallerSetup
import UInt256.Safety.OutputAccess
import UInt256.Safety.ArgumentValues
import CIL.Safety.StepComposition
import CIL.Safety.ExecutionLifetime
import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.ReturnMemory
import CIL.Safety.GuardNormalization
import CIL.Safety.MethodContract

namespace UInt256Model.Safety
open CIL.Safety

/-- Remembered typed locals; a missing entry grants no initialization or value fact. -/
def KnownLocals (memory : Memory) (slots : List LocalSlot) (known : Nat → Option CIL.Value) : Prop :=
  ∀ index value, known index = some value →
    ∃ kind reference number, slots[index]? = some (.bytes kind reference) ∧
      localNumber kind value = .ok number ∧ localResult kind value = value ∧
      CIL.Safety.read memory reference (localWidth kind) 1 = .ok (numberBytes number (localWidth kind))

def rememberLocal (known : Nat → Option CIL.Value) (index : Nat) (value : CIL.Value) :
    Nat → Option CIL.Value := fun other => if other = index then some value else known other

theorem NumericHomes.writable {memory : Memory} {lower : Nat} {specs slots}
    (homes : NumericHomes memory lower specs slots) :
    WritableHomes memory lower (numericKinds specs) slots := by
  induction homes with
  | nil lower => exact .nil lower
  | cons reference spec fresh _ writable _ ih => exact .cons reference spec.kind fresh writable ih

/-- Unchanged bytes of every remembered home, with retained authority, keep the snapshots. -/
theorem KnownLocals.preserve {before after : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (locals : KnownLocals before slots known)
    (wf : before.WellFormed) (authority : AccessBelow before.nextIdentity before after)
    (unchanged : ∀ index value, known index = some value → ∀ kind reference,
      slots[index]? = some (.bytes kind reference) → ∀ offset,
        after.cells reference.allocation offset = before.cells reference.allocation offset) :
    KnownLocals after slots known := by
  intro index value specified
  obtain ⟨kind, reference, number, slot, fits, result, loaded⟩ := locals index value specified
  have ready := read_access loaded
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have old := (wf.1 _ _ requirements.present).1
  exact ⟨kind, reference, number, slot, fits, result,
    authority.read_eq loaded old (fun i _ => unchanged index value specified kind reference slot _)⟩

/-- A frame's remembered locals, its caller-visible effects so far and the output contents. -/
structure VectorFrame (program : CIL.Program) (original entered current : Memory)
    (inputs : List Reference) (output : Reference) (frame : Frame)
    (known : Nat → Option CIL.Value) (stored : Option (BitVec 256)) : Prop where
  call : CallingConditions program current inputs [output]
  enteredWF : entered.WellFormed
  enteredBound : original.nextIdentity ≤ entered.nextIdentity
  next : entered.nextIdentity ≤ current.nextIdentity
  authority : AccessBelow entered.nextIdentity entered current
  locals : KnownLocals current frame.locals known
  caller : ∀ id, id < original.nextIdentity → ∀ offset, (stored = none ∨ OutsideOutput output id offset) →
    current.cells id offset = original.cells id offset
  result : ∀ value, stored = some value → read current output 32 1 = .ok (numberBytes value.toNat 32)

theorem VectorFrame.output_old {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    (_state : VectorFrame program original entered current inputs output frame known stored)
    (originalCall : CallingConditions program original inputs [output]) :
    output.allocation < original.nextIdentity := by
  have formed := originalCall.output_formed (by simp : output ∈ [output])
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ formed
  exact (originalCall.1.1.1 _ _ present).1

/-- The callee's fresh frame starts with no remembered locals and the caller's memory. -/
theorem VectorFrame.initial {program : CIL.Program} {original entered : Memory}
    {inputs : List Reference} {output : Reference} {body : CIL.Method} {args : List Value}
    {frame : Frame} (call : CallingConditions program original inputs [output])
    (setup : enterFrame body args original = .ok (frame, entered)) :
    VectorFrame program original entered entered inputs output frame (fun _ => none) none := by
  refine ⟨call.after_frame_setup setup, ?_, (enterFrame_fresh _ _ _ _ _ setup).1.next,
    Nat.le_refl _, (MemoryBelow.refl _ _).accessBelow, ?_, ?_, ?_⟩
  · exact enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  · intro index value impossible
    cases impossible
  · intro id old offset _
    exact (enterFrame_preserves_caller_memory _ _ _ _ _ setup).cells id old offset
  · intro value impossible
    cases impossible

theorem VectorFrame.load {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    (state : VectorFrame program original entered current inputs output frame known stored)
    {body : CIL.Method} {pc index : Nat} {args stack : List Value} {value : CIL.Value}
    (specified : known index = some value) :
    step body (.local index) pc args frame stack current =
      .ok (.next (pc + 1) (.scalar value :: stack) frame current) := by
  obtain ⟨kind, reference, number, slot, fits, result, loaded⟩ := state.locals index value specified
  have stepped := step_load_numeric_local (body := body) (pc := pc) (args := args) (stack := stack)
    kind value number fits slot loaded
  rwa [result] at stepped

/-- A typed local store remembers its value and changes only that private home. -/
theorem VectorFrame.store {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    (state : VectorFrame program original entered current inputs output frame known stored)
    (originalCall : CallingConditions program original inputs [output])
    {kinds : List CIL.LocalKind} (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (specified : kinds[index]? = some kind) (fits : localNumber kind value = .ok number)
    (result : localResult kind value = value) :
    ∃ after,
      step body (.setLocal index) pc args frame (.scalar value :: stack) current =
        .ok (.next (pc + 1) stack frame after) ∧
      VectorFrame program original entered after inputs output frame
        (rememberLocal known index value) stored := by
  obtain ⟨reference, slot, bound, ready⟩ := homes.home_at index kind specified
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have privateOld := (state.enteredWF.1 _ _ requirements.present).1
  have writable := state.authority.access ready privateOld
  obtain ⟨after, stepped, written, readback⟩ := step_store_numeric_local
    (body := body) (pc := pc) (args := args) (rest := stack) kind value number fits slot writable
  have outputOld := state.output_old originalCall
  have outside : ∀ id, id ≠ reference.allocation → ∀ offset,
      after.cells id offset = current.cells id offset := fun id different offset =>
    write_outside _ _ _ _ _ id offset written (Or.inl different)
  refine ⟨after, stepped, state.call.after_write written, state.enteredWF, state.enteredBound,
    Nat.le_trans state.next (write_extends_allocations _ _ _ _ _ written).next,
    state.authority.trans (write_preserves_access_below written _), ?_, ?_, ?_⟩
  · intro other otherValue otherSpecified
    by_cases same : other = index
    · subst other
      have sameValue : value = otherValue := by simpa [rememberLocal] using otherSpecified
      subst otherValue
      exact ⟨kind, reference, number, slot, fits, result, readback⟩
    · have previous : known other = some otherValue := by
        simpa [rememberLocal, same] using otherSpecified
      let others : Nat → Option CIL.Value := fun i => if i = index then none else known i
      have restricted : KnownLocals current frame.locals others := by
        intro i v specifiedI
        by_cases hi : i = index
        · simp [others, hi] at specifiedI
        · exact state.locals i v (by simpa [others, hi] using specifiedI)
      have kept := restricted.preserve state.call.1.1 (write_preserves_access_below written _)
        (fun i v specifiedI k r slotI offset => by
          by_cases hi : i = index
          · simp [others, hi] at specifiedI
          · exact outside _ (homes.distinct i index k kind r reference hi slotI slot) offset)
      exact kept other otherValue (by simpa [others, same] using previous)
  · intro id old offset away
    have different : id ≠ reference.allocation := by omega
    exact (outside id different offset).trans (state.caller id old offset away)
  · intro x specifiedX
    have loaded := state.result x specifiedX
    have ready := read_access loaded
    have different : output.allocation ≠ reference.allocation := fun same =>
      Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (same ▸ outputOld) bound)
    exact (write_preserves_access_below written current.nextIdentity).read_eq loaded
      (by
        obtain ⟨a, req⟩ := access_requirements ready
        exact (state.call.1.1.1 _ _ req.present).1)
      (fun i _ => outside _ different _)

/-- A typed local load pushes the remembered value. -/
theorem VectorFrame.run_load {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {body : CIL.Method} {method pc index : Nat} {args stack : List Value} {value : CIL.Value}
    (post : Memory → List Value → Prop)
    (state : VectorFrame program original entered current inputs output frame known stored)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.local index))
    (specified : known index = some value)
    (continuation : ∃ fuel result returned,
      run program fuel method (pc + 1) args frame (.scalar value :: stack) current = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack current = .ok (result, returned) ∧ post result returned :=
  run_next_exists post found fetched (state.load specified) continuation

/-- A typed local store remembers its value; the continuation receives the new state. -/
theorem VectorFrame.run_store {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {kinds : List CIL.LocalKind} {body : CIL.Method} {method pc index number : Nat}
    {args stack : List Value} {kind : CIL.LocalKind} {value : CIL.Value}
    (post : Memory → List Value → Prop)
    (state : VectorFrame program original entered current inputs output frame known stored)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.setLocal index))
    (specified : kinds[index]? = some kind) (fits : localNumber kind value = .ok number)
    (result : localResult kind value = value)
    (continuation : ∀ after,
      VectorFrame program original entered after inputs output frame (rememberLocal known index value) stored →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame stack after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame (.scalar value :: stack) current = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨after, stepped, next⟩ := state.store originalCall homes (body := body) (pc := pc) (args := args)
    (stack := stack) kind value number specified fits result
  exact run_next_exists post found fetched stepped (continuation after next)

/-- A 256-bit store to the output records its value and keeps every private home and other caller byte. -/
theorem VectorFrame.output_store {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {kinds : List CIL.LocalKind}
    (state : VectorFrame program original entered current inputs output frame known stored)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (body : CIL.Method) (pc : Nat) (args rest : List Value) (value : BitVec 256) :
    ∃ after,
      step body (.memory .store256) pc args frame
        (.scalar (.v256 value) :: .reference (.address output) :: rest) current =
        .ok (.next (pc + 1) rest frame after) ∧
      VectorFrame program original entered after inputs output frame known (some value) := by
  have length : (numberBytes value.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨after, written, afterCall, outside, readback⟩ :=
    state.call.write_output_slice (by simp : output ∈ [output]) 0 (numberBytes value.toNat 32)
      (by rw [length]; decide) (by rw [length]; decide)
  have self : { output with offset := output.offset + 0 } = output := by cases output; rfl
  rw [self] at written readback
  rw [length] at readback
  have outputOld := state.output_old originalCall
  have separate (index : Nat) (kind : CIL.LocalKind) (reference : Reference)
      (slot : frame.locals[index]? = some (.bytes kind reference)) :
      reference.allocation ≠ output.allocation := fun same =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (same ▸ outputOld) (homes.home_bound index kind reference slot))
  refine ⟨after, ?_, afterCall, state.enteredWF, state.enteredBound,
    Nat.le_trans state.next (write_extends_allocations _ _ _ _ _ written).next,
    state.authority.trans (write_preserves_access_below written _), ?_, ?_, ?_⟩
  · simp [step, cil_guard, observerCount, staticInstruction, memoryInstruction, storeValue, referenceAt, ordinaryAccessAlignment,
      written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro index entry specified
    obtain ⟨kind, reference, number, slot, fits, result, loaded⟩ := state.locals index entry specified
    exact ⟨kind, reference, number, slot, fits, result,
      write_preserves_disjoint_read written loaded (Or.inl (separate index kind reference slot))⟩
  · intro id old offset away
    have away := away.resolve_left (by simp)
    exact (outside id offset away).trans (state.caller id old offset (Or.inr away))
  · intro x same
    cases same
    exact readback

/-- An invoked helper that keeps all bytes below the current boundary keeps every remembered fact. -/
theorem VectorFrame.after_call {program : CIL.Program} {original entered current after : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    (state : VectorFrame program original entered current inputs output frame known stored)
    (preserved : MemoryBelow current.nextIdentity current after) (wf : after.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) after)
    (grown : current.nextIdentity ≤ after.nextIdentity) :
    VectorFrame program original entered after inputs output frame known stored := by
  have older (id : Nat) (old : id < original.nextIdentity) : id < current.nextIdentity :=
    Nat.lt_of_lt_of_le old (Nat.le_trans state.enteredBound state.next)
  refine ⟨state.call.after_memory_below preserved wf world, state.enteredWF, state.enteredBound,
    Nat.le_trans state.next grown, state.authority.trans (preserved.accessBelow.weaken state.next), ?_, ?_, ?_⟩
  · intro index value specified
    obtain ⟨kind, reference, number, slot, fits, result, loaded⟩ := state.locals index value specified
    have ready := read_access loaded
    obtain ⟨allocation, requirements⟩ := access_requirements ready
    exact ⟨kind, reference, number, slot, fits, result,
      (preserved.read reference (state.call.1.1.1 _ _ requirements.present).1 _ _).trans loaded⟩
  · intro id old offset away
    exact (preserved.cells id (older id old) offset).trans (state.caller id old offset away)
  · intro value specified
    have loaded := state.result value specified
    have ready := read_access loaded
    obtain ⟨allocation, requirements⟩ := access_requirements ready
    exact (preserved.read output (state.call.1.1.1 _ _ requirements.present).1 _ _).trans loaded

/-- Leaving the frame exposes the stored output, its authority and the other original caller bytes. -/
theorem VectorFrame.finish {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {value : BitVec 256}
    (state : VectorFrame program original entered current inputs output frame known (some value))
    (originalCall : CallingConditions program original inputs [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    inputValue (leaveFrame frame current) output = value ∧
      access (leaveFrame frame current) output 32 1 true = .ok () ∧
      ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
        (leaveFrame frame current).cells id offset = original.cells id offset := by
  have retained := leaveFrame_preserves_memory_below frame current original.nextIdentity owned
  have old := state.output_old originalCall
  have loaded := state.result value rfl
  refine ⟨?_, (retained.access output old 32 1 true).trans
    (state.call.1.2.2 (wordView output) (by simp)), ?_⟩
  · exact inputValue_of_encoded_read ((retained.read output old 32 1).trans loaded)
  · intro id bound offset away
    exact (retained.cells id bound offset).trans (state.caller id bound offset (Or.inr away))

/-- Before the first output store, every input still holds its initial value. -/
theorem VectorFrame.input_value {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value}
    (state : VectorFrame program original entered current inputs output frame known none)
    (originalCall : CallingConditions program original inputs [output])
    {input : Reference} (member : input ∈ inputs) :
    inputValue current input = inputValue original input := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (originalCall.input_formed member)
  have old := (originalCall.1.1.1 _ _ present).1
  unfold inputValue
  congr 2
  funext offset
  rw [state.caller input.allocation old offset (Or.inl rfl)]

#print axioms VectorFrame.input_value
#print axioms VectorFrame.run_load
#print axioms VectorFrame.run_store
#print axioms VectorFrame.output_store
#print axioms VectorFrame.after_call
#print axioms VectorFrame.finish
end UInt256Model.Safety
