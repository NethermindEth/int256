import UInt256.Safety.VectorFrame
import CIL.Safety.ByteEncoding

namespace UInt256Model.Safety
open CIL.Safety

/-- Caller cells reached through reference arguments: writable, holding each remembered 256-bit value. -/
def ScratchCells (memory : Memory) (cells : List Reference) (known : Nat → Option (BitVec 256)) : Prop :=
  ∀ (index : Nat) (cell : Reference), cells[index]? = some cell →
    access memory cell 32 1 true = .ok () ∧
      ∀ value, known index = some value → CIL.Safety.read memory cell 32 1 = .ok (numberBytes value.toNat 32)

/-- Scratch cells occupy distinct allocations in `[lower, upper)`. -/
structure ScratchLayout (lower upper : Nat) (cells : List Reference) : Prop where
  bounds : ∀ (index : Nat) (cell : Reference), cells[index]? = some cell →
    lower ≤ cell.allocation ∧ cell.allocation < upper
  distinct : ∀ (i j : Nat) (first second : Reference), i ≠ j → cells[i]? = some first → cells[j]? = some second →
    first.allocation ≠ second.allocation

def rememberCell (known : Nat → Option (BitVec 256)) (index : Nat) (value : BitVec 256) :
    Nat → Option (BitVec 256) := fun other => if other = index then some value else known other

theorem ScratchCells.after_write {memory after : Memory} {cells : List Reference}
    {known : Nat → Option (BitVec 256)} {target : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (scratch : ScratchCells memory cells known) (written : write memory target bytes alignment = .ok after)
    (away : ∀ (index : Nat) (cell : Reference), cells[index]? = some cell → cell.allocation ≠ target.allocation) :
    ScratchCells after cells known := by
  intro index cell found
  obtain ⟨writable, values⟩ := scratch index cell found
  refine ⟨(write_preserves_access_below written (cell.allocation + 1)).access writable (Nat.lt_succ_self _), ?_⟩
  intro value specified
  exact write_preserves_disjoint_read written (values value specified) (Or.inl (away index cell found))

theorem ScratchCells.after_below {memory after : Memory} {cells : List Reference}
    {known : Nat → Option (BitVec 256)} {watermark : Nat}
    (scratch : ScratchCells memory cells known) (preserved : MemoryBelow watermark memory after)
    (old : ∀ (index : Nat) (cell : Reference), cells[index]? = some cell → cell.allocation < watermark) :
    ScratchCells after cells known := by
  intro index cell found
  obtain ⟨writable, values⟩ := scratch index cell found
  refine ⟨(preserved.access cell (old index cell found) 32 1 true).trans writable, ?_⟩
  intro value specified
  exact (preserved.read cell (old index cell found) 32 1).trans (values value specified)

/-- Writing one cell remembers its value and keeps every other cell. -/
theorem ScratchCells.write_cell {memory : Memory} {cells : List Reference}
    {known : Nat → Option (BitVec 256)} {lower upper : Nat}
    (scratch : ScratchCells memory cells known) (layout : ScratchLayout lower upper cells)
    {index : Nat} {cell : Reference} (found : cells[index]? = some cell) (value : BitVec 256) :
    ∃ after, write memory cell (numberBytes value.toNat 32) 1 = .ok after ∧
      ScratchCells after cells (rememberCell known index value) := by
  have length : (numberBytes value.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨writable, _⟩ := scratch index cell found
  obtain ⟨after, written⟩ := write_succeeds (bytes := numberBytes value.toNat 32) (alignment := 1)
    (by rw [length]; exact writable)
  refine ⟨after, written, ?_⟩
  intro other target targetFound
  obtain ⟨targetWritable, targetValues⟩ := scratch other target targetFound
  refine ⟨(write_preserves_access_below written (target.allocation + 1)).access targetWritable
    (Nat.lt_succ_self _), ?_⟩
  intro stored specified
  by_cases same : other = index
  · subst other
    rw [found] at targetFound
    cases targetFound
    have equal : value = stored := by simpa [rememberCell] using specified
    subst equal
    have readback := write_readback _ _ _ _ _ written
    rwa [length] at readback
  · have previous : known other = some stored := by simpa [rememberCell, same] using specified
    exact write_preserves_disjoint_read written (targetValues stored previous)
      (Or.inl (layout.distinct other index target cell same targetFound found))

theorem vector_bytes_decode (vector : BitVec 256) :
    BitVec.ofNat 256 (CIL.Safety.byteNumber (numberBytes vector.toNat 32)) = vector := by
  rw [byteNumber_numberBytes]
  have bound : vector.toNat < 256^32 := vector.isLt
  rw [Nat.mod_eq_of_lt bound]
  simp

theorem scratch_load {memory : Memory} {cell : Reference} {value : BitVec 256}
    (loaded : CIL.Safety.read memory cell 32 1 = .ok (numberBytes value.toNat 32)) :
    loadValue memory (.address cell) 32 = .ok (.v256 value) := by
  simp only [loadValue, dereference, loaded, checkedAt, ordinaryAccessAlignment, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [vector_bytes_decode]

/-- Remembered cells that are typed vector homes of a frame give its remembered locals. -/
theorem ScratchCells.known_locals {memory : Memory} {cells : List Reference}
    {known : Nat → Option (BitVec 256)} {slots : List LocalSlot}
    (scratch : ScratchCells memory cells known)
    (homes : ∀ (index : Nat) (cell : Reference), cells[index]? = some cell →
      slots[index]? = some (LocalSlot.bytes .vector256 cell))
    (defined : ∀ (index : Nat) (value : BitVec 256), known index = some value →
      ∃ cell : Reference, cells[index]? = some cell) :
    KnownLocals memory slots (fun index => (known index).map .v256) := by
  intro index value specified
  obtain ⟨stored, remembered, rfl⟩ := Option.map_eq_some_iff.mp specified
  obtain ⟨cell, found⟩ := defined index stored remembered
  exact ⟨.vector256, cell, stored.toNat, homes index cell found, rfl, rfl,
    (scratch index cell found).2 stored remembered⟩

theorem CallingConditions.without_inputs {program : CIL.Program} {memory : Memory}
    {inputs outputs : List Reference} (call : CallingConditions program memory inputs outputs) :
    CallingConditions program memory [] outputs :=
  ⟨⟨call.1.1, fun _ member => by simp at member, call.1.2.2⟩, call.2⟩

/-- Views valid at an older boundary survive any change that keeps the bytes below it. -/
theorem CallingConditions.retained {program : CIL.Program} {original memory updated : Memory}
    {inputs outputs : List Reference}
    (origin : CallingConditions program original inputs outputs)
    (call : CallingConditions program memory inputs outputs)
    (preserved : MemoryBelow original.nextIdentity memory updated) (wellFormed : updated.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) updated) :
    CallingConditions program updated inputs outputs := by
  refine ⟨⟨wellFormed, ?_, ?_⟩, world⟩
  · intro input member
    obtain ⟨bytes, loaded⟩ := call.1.2.1 input member
    obtain ⟨old, oldLoaded⟩ := origin.1.2.1 input member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
      (read_reference_valid _ _ _ _ _ oldLoaded)
    exact ⟨bytes, (preserved.read input.reference (origin.1.1.1 _ _ present).1 _ _).trans loaded⟩
  · intro output member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (origin.1.2.2 output member)
    exact (preserved.access output.reference (origin.1.1.1 _ _ present).1 _ _ _).trans (call.1.2.2 output member)

/-- A frame entered from a caller memory that still agrees with an older original memory. -/
theorem VectorFrame.initial_from {program : CIL.Program} {original memory entered : Memory}
    {inputs : List Reference} {output : Reference} {body : CIL.Method} {args : List Value}
    {frame : Frame} (call : CallingConditions program memory inputs [output])
    (grown : original.nextIdentity ≤ memory.nextIdentity)
    (same : ∀ id, id < original.nextIdentity → ∀ offset, memory.cells id offset = original.cells id offset)
    (setup : enterFrame body args memory = .ok (frame, entered)) :
    VectorFrame program original entered entered inputs output frame (fun _ => none) none := by
  have below := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  refine ⟨call.after_frame_setup setup, ?_, Nat.le_trans grown (enterFrame_fresh _ _ _ _ _ setup).1.next,
    Nat.le_refl _, (MemoryBelow.refl _ _).accessBelow, ?_, ?_, ?_⟩
  · exact enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  · intro index value impossible
    cases impossible
  · intro id old offset _
    exact (below.cells id (Nat.lt_of_lt_of_le old grown) offset).trans (same id old offset)
  · intro value impossible
    cases impossible

/-- A typed local store keeps the frame facts and every scratch cell below the private homes. -/
theorem VectorFrame.run_store_scratch {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {kinds : List CIL.LocalKind} {body : CIL.Method} {method pc index number upper : Nat}
    {args stack : List Value} {kind : CIL.LocalKind} {value : CIL.Value}
    {cells : List Reference} {cellValues : Nat → Option (BitVec 256)}
    (post : Memory → List Value → Prop)
    (state : VectorFrame program original entered current inputs output frame known stored)
    (scratch : ScratchCells current cells cellValues)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered upper kinds frame.locals) (bound : original.nextIdentity ≤ upper)
    (layout : ScratchLayout original.nextIdentity upper cells)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.setLocal index))
    (specified : kinds[index]? = some kind) (fits : localNumber kind value = .ok number)
    (result : localResult kind value = value)
    (continuation : ∀ after,
      VectorFrame program original entered after inputs output frame (rememberLocal known index value) stored →
      ScratchCells after cells cellValues →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame stack after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame (.scalar value :: stack) current = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨after, stepped, next⟩ := state.store originalCall (homes.weaken bound) (body := body) (pc := pc)
    (args := args) (stack := stack) kind value number specified fits result
  obtain ⟨reference, slot, homeBound, ready⟩ := homes.home_at index kind specified
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have privateOld := (state.enteredWF.1 _ _ requirements.present).1
  have writable := state.authority.access ready privateOld
  obtain ⟨written, stepWritten, write, _⟩ := step_store_numeric_local
    (body := body) (pc := pc) (args := args) (rest := stack) kind value number fits slot writable
  rw [stepped] at stepWritten
  have same : after = written := by
    injection stepWritten with action
    injection action
  subst same
  exact run_next_exists post found fetched stepped (continuation after next
    (ScratchCells.after_write scratch write (fun i cell cellFound =>
      Nat.ne_of_lt (Nat.lt_of_lt_of_le (layout.bounds i cell cellFound).2 homeBound))))

/-- A 256-bit output store keeps every scratch cell above the caller boundary. -/
theorem VectorFrame.output_store_scratch {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {kinds : List CIL.LocalKind} {upper : Nat}
    {cells : List Reference} {cellValues : Nat → Option (BitVec 256)}
    (state : VectorFrame program original entered current inputs output frame known stored)
    (scratch : ScratchCells current cells cellValues)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (layout : ScratchLayout original.nextIdentity upper cells)
    (body : CIL.Method) (pc : Nat) (args rest : List Value) (value : BitVec 256) :
    ∃ after,
      step body (.memory .store256) pc args frame
        (.scalar (.v256 value) :: .reference (.address output) :: rest) current =
        .ok (.next (pc + 1) rest frame after) ∧
      VectorFrame program original entered after inputs output frame known (some value) ∧
      ScratchCells after cells cellValues := by
  obtain ⟨after, stepped, next⟩ := state.output_store originalCall homes body pc args rest value
  have length : (numberBytes value.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨written, write, _, _, _⟩ :=
    state.call.write_output_slice (by simp : output ∈ [output]) 0 (numberBytes value.toNat 32)
      (by rw [length]; decide) (by rw [length]; decide)
  have self : { output with offset := output.offset + 0 } = output := by cases output; rfl
  rw [self] at write
  have mine : step body (.memory .store256) pc args frame
      (.scalar (.v256 value) :: .reference (.address output) :: rest) current =
      .ok (.next (pc + 1) rest frame written) := by
    simp [step, cil_guard, observerCount, staticInstruction, memoryInstruction, storeValue, referenceAt, ordinaryAccessAlignment,
      write, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [stepped] at mine
  have same : after = written := by
    injection mine with action
    injection action
  subst same
  have outputOld := state.output_old originalCall
  exact ⟨after, stepped, next, ScratchCells.after_write scratch write (fun i cell cellFound =>
    Nat.ne_of_gt (Nat.lt_of_lt_of_le outputOld (layout.bounds i cell cellFound).1))⟩

/-- A 256-bit store to a scratch cell remembers it and keeps every frame fact. -/
theorem VectorFrame.cell_store {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {kinds : List CIL.LocalKind} {upper : Nat}
    {cells : List Reference} {cellValues : Nat → Option (BitVec 256)}
    (state : VectorFrame program original entered current inputs output frame known stored)
    (scratch : ScratchCells current cells cellValues)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered upper kinds frame.locals)
    (layout : ScratchLayout original.nextIdentity upper cells)
    {index : Nat} {cell : Reference} (cellFound : cells[index]? = some cell)
    (body : CIL.Method) (pc : Nat) (args rest : List Value) (value : BitVec 256) :
    ∃ after,
      step body (.memory .store256) pc args frame
        (.scalar (.v256 value) :: .reference (.address cell) :: rest) current =
        .ok (.next (pc + 1) rest frame after) ∧
      VectorFrame program original entered after inputs output frame known stored ∧
      ScratchCells after cells (rememberCell cellValues index value) := by
  obtain ⟨after, write, next⟩ := scratch.write_cell layout cellFound value
  have bounds := layout.bounds index cell cellFound
  have outputOld := state.output_old originalCall
  refine ⟨after, ?_, ⟨state.call.after_write write, state.enteredWF, state.enteredBound,
    Nat.le_trans state.next (write_extends_allocations _ _ _ _ _ write).next,
    state.authority.trans (write_preserves_access_below write _), ?_, ?_, ?_⟩, next⟩
  · simp [step, cil_guard, observerCount, staticInstruction, memoryInstruction, storeValue, referenceAt, ordinaryAccessAlignment,
      write, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro other entry specified
    obtain ⟨kind, reference, number, slot, fits, result, loaded⟩ := state.locals other entry specified
    have home := homes.home_bound other kind reference slot
    exact ⟨kind, reference, number, slot, fits, result, write_preserves_disjoint_read write loaded
      (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le bounds.2 home)))⟩
  · intro id old offset away
    exact (write_outside _ _ _ _ _ id offset write (Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le old bounds.1)))).trans
      (state.caller id old offset away)
  · intro x specified
    exact write_preserves_disjoint_read write (state.result x specified)
      (Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld bounds.1)))

/-- Leaving the frame exposes the encoded stored output. -/
theorem VectorFrame.finish_read {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {value : BitVec 256}
    (state : VectorFrame program original entered current inputs output frame known (some value))
    (originalCall : CallingConditions program original inputs [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    CIL.Safety.read (leaveFrame frame current) output 32 1 = .ok (numberBytes value.toNat 32) :=
  ((leaveFrame_preserves_memory_below frame current original.nextIdentity owned).read output
    (state.output_old originalCall) 32 1).trans (state.result value rfl)

/-- A child that wrote the output and kept other caller bytes completes the frame's caller guarantees. -/
theorem VectorFrame.finish_child {program : CIL.Program} {original entered current after : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)} {value : BitVec 256}
    (state : VectorFrame program original entered current inputs output frame known stored)
    (originalCall : CallingConditions program original inputs [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (result : CIL.Safety.read after output 32 1 = .ok (numberBytes value.toNat 32))
    (writable : access after output 32 1 true = .ok ())
    (footprint : ∀ id, id < current.nextIdentity → ∀ offset, OutsideOutput output id offset →
      after.cells id offset = current.cells id offset) :
    inputValue (leaveFrame frame after) output = value ∧
      access (leaveFrame frame after) output 32 1 true = .ok () ∧
      ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
        (leaveFrame frame after).cells id offset = original.cells id offset := by
  have retained := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  have old := state.output_old originalCall
  refine ⟨inputValue_of_encoded_read ((retained.read output old 32 1).trans result),
    (retained.access output old 32 1 true).trans writable, ?_⟩
  intro id bound offset away
  exact (retained.cells id bound offset).trans ((footprint id
    (Nat.lt_of_lt_of_le bound (Nat.le_trans state.enteredBound state.next)) offset away).trans
    (state.caller id bound offset (Or.inr away)))

/-- A child that kept caller bytes outside the output and stored it gives the next frame state. -/
theorem VectorFrame.after_child {program : CIL.Program} {original entered current after : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known known' : Nat → Option CIL.Value} {stored : Option (BitVec 256)} {value : BitVec 256}
    (state : VectorFrame program original entered current inputs output frame known stored)
    (call : CallingConditions program after inputs [output])
    (grown : current.nextIdentity ≤ after.nextIdentity)
    (authority : AccessBelow current.nextIdentity current after)
    (footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
      after.cells id offset = original.cells id offset)
    (result : CIL.Safety.read after output 32 1 = .ok (numberBytes value.toNat 32))
    (locals : KnownLocals after frame.locals known') :
    VectorFrame program original entered after inputs output frame known' (some value) :=
  ⟨call, state.enteredWF, state.enteredBound, Nat.le_trans state.next grown,
    state.authority.trans (authority.weaken state.next), locals,
    fun id old offset away => footprint id old offset (away.resolve_left (by simp)),
    fun x same => by cases same; exact result⟩

/-- Loading a remembered cell pushes its value. -/
theorem run_cell_load {program : CIL.Program} {body : CIL.Method} {method pc : Nat}
    {args stack : List Value} {frame : Frame} {current : Memory} {cell : Reference} {value : BitVec 256}
    (post : Memory → List Value → Prop)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.memory .load256))
    (loaded : CIL.Safety.read current cell 32 1 = .ok (numberBytes value.toNat 32))
    (continuation : ∃ fuel result returned,
      run program fuel method (pc + 1) args frame (.scalar (.v256 value) :: stack) current =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame (.reference (.address cell) :: stack) current =
        .ok (result, returned) ∧ post result returned := by
  apply run_next_exists post found fetched _ continuation
  simp [step, cil_guard, observerCount, staticInstruction, memoryInstruction, scratch_load loaded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A 256-bit store to a scratch cell; the continuation receives the updated frame and cells. -/
theorem VectorFrame.run_cell_store {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {kinds : List CIL.LocalKind} {upper : Nat}
    {cells : List Reference} {cellValues : Nat → Option (BitVec 256)}
    {body : CIL.Method} {method pc : Nat} {args rest : List Value} {value : BitVec 256}
    (post : Memory → List Value → Prop)
    (state : VectorFrame program original entered current inputs output frame known stored)
    (scratch : ScratchCells current cells cellValues)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered upper kinds frame.locals)
    (layout : ScratchLayout original.nextIdentity upper cells)
    (index : Nat) {cell : Reference} (cellFound : cells[index]? = some cell)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.memory .store256))
    (continuation : ∀ after,
      VectorFrame program original entered after inputs output frame known stored →
      ScratchCells after cells (rememberCell cellValues index value) →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame rest after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame (.scalar (.v256 value) :: .reference (.address cell) :: rest) current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, stepped, next, cellsNext⟩ :=
    state.cell_store scratch originalCall homes layout cellFound body pc args rest value
  exact run_next_exists post found fetched stepped (continuation after next cellsNext)

/-- A 256-bit output store; the continuation receives the stored frame and the unchanged cells. -/
theorem VectorFrame.run_output_store {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {kinds : List CIL.LocalKind} {upper : Nat}
    {cells : List Reference} {cellValues : Nat → Option (BitVec 256)}
    {body : CIL.Method} {method pc : Nat} {args rest : List Value} {value : BitVec 256}
    (post : Memory → List Value → Prop)
    (state : VectorFrame program original entered current inputs output frame known stored)
    (scratch : ScratchCells current cells cellValues)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (layout : ScratchLayout original.nextIdentity upper cells)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.memory .store256))
    (continuation : ∀ after,
      VectorFrame program original entered after inputs output frame known (some value) →
      ScratchCells after cells cellValues →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame rest after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame (.scalar (.v256 value) :: .reference (.address output) :: rest)
        current = .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, stepped, next, cellsNext⟩ :=
    state.output_store_scratch scratch originalCall homes layout body pc args rest value
  exact run_next_exists post found fetched stepped (continuation after next cellsNext)

#print axioms run_cell_load
#print axioms VectorFrame.run_cell_store
#print axioms VectorFrame.run_output_store
#print axioms ScratchCells.write_cell
#print axioms scratch_load
#print axioms ScratchCells.known_locals
#print axioms CallingConditions.retained
#print axioms VectorFrame.initial_from
#print axioms VectorFrame.run_store_scratch
#print axioms VectorFrame.output_store_scratch
#print axioms VectorFrame.cell_store
#print axioms VectorFrame.finish_read
#print axioms VectorFrame.finish_child
#print axioms VectorFrame.after_child
end UInt256Model.Safety
