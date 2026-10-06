import UInt256.Methods.Add.CarryContract
import UInt256.Safety.CallerSetup

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- A carry helper writing private homes preserves caller input snapshots.
    Input views may still overlap one another or the caller's output freely. -/
theorem CarryPost.private_input_bytes {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions Extracted.program before inputs outputs)
    {reference : Reference} (member : reference ∈ inputs)
    (notCarry : reference.allocation ≠ carryRef.allocation)
    (notOutput : reference.allocation ≠ output.allocation) :
    (fun offset => (after.cells reference.allocation offset).bits) =
      (fun offset => (before.cells reference.allocation offset).bits) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  have old := (call.1.1.1 _ _ present).1
  funext offset
  rw [post.footprint _ _ old (Or.inl notCarry) (Or.inl notOutput)]

/-- Retain read/write authority, original readable input bytes and static data
    across the actual helper invocation. Exact permission equality is not needed. -/
theorem CarryPost.private_calling_conditions {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions Extracted.program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ carryRef.allocation ∧ reference.allocation ≠ output.allocation) :
    CallingConditions Extracted.program after inputs outputs := by
  refine ⟨⟨post.wellFormed, ?_, ?_⟩, post.staticWorld call.2⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed inputMember)
    have old := (call.1.1.1 _ _ present).1
    obtain ⟨notCarry, notOutput⟩ := separate reference inputMember
    refine ⟨_, post.access.read_eq (call.input_snapshot inputMember) old ?_⟩
    intro i _
    exact post.footprint _ _ old (Or.inl notCarry) (Or.inl notOutput)
  · intro view member
    have writable := call.1.2.2 view member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
    exact post.access.access writable (call.1.1.1 _ _ present).1

theorem CarryPost.private_input_field {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions Extracted.program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ carryRef.allocation ∧ reference.allocation ≠ output.allocation)
    {reference : Reference} (member : reference ∈ inputs) (index : Fin 4) (rest : List Value) :
    instruction (.field index) (.reference (.address reference) :: rest) after =
      .ok (after, .scalar (.i64 (inputLimb before reference index)) :: rest) := by
  rw [(post.private_calling_conditions call separate).input_field_instruction member index rest]
  simp only [inputLimb, post.private_input_bytes call member (separate reference member).1
    (separate reference member).2]

#print axioms CarryPost.private_input_bytes
#print axioms CarryPost.private_calling_conditions
#print axioms CarryPost.private_input_field

end UInt256Proof.Safety

namespace UInt256Proof.Safety
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
  call : CallingConditions Extracted.program current [left, right] [output]
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

/-- A checked carry invocation advances the same parent invariant, retaining
    initial operand snapshots and every previously completed result home. -/
theorem ScalarCarryState.advance {original before after : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} {carryIndex resultBase : Nat} (index : Fin 4)
    (state : ScalarCarryState original before frame left right output carryHome results index.val carryIndex resultBase)
    (math : CarryPost (inputLimb original left index) (inputLimb original right index)
      (scalarCarryValue original left right index.val) carryHome (results index) before after) :
    ScalarCarryState original after frame left right output carryHome results (index.val + 1) carryIndex resultBase := by
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
  refine ⟨math.private_calling_conditions state.call separate, ?_, state.carrySlot, state.resultSlots,
    math.access.access state.carryWrite carryOld,
    fun i => math.access.access (state.resultWrites i) (resultOld i), ?_, ?_,
    state.callerSeparate, state.carrySeparate, state.resultSeparate,
    state.carryFresh, state.resultsFresh, ?_, ?_⟩
  · intro reference member
    exact (math.private_input_bytes state.call member (separate reference member).1
      (separate reference member).2).trans (state.inputBytes reference member)
  · simpa only [scalarCarryValue, dite_eq_left index.isLt] using math.carryBytes
  · simpa only [scalarCarryValue, dite_eq_left index.isLt] using math.carryBound
  · intro id old offset
    have belowCarry := Nat.lt_of_lt_of_le old state.carryFresh
    have belowResult := Nat.lt_of_lt_of_le old (state.resultsFresh index)
    exact (math.footprint id offset (Nat.lt_trans belowCarry carryOld)
      (Or.inl (Nat.ne_of_lt belowCarry)) (Or.inl (Nat.ne_of_lt belowResult))).trans
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
      exact math.footprint _ _ (resultOld i) (Or.inl (state.carrySeparate i))
        (Or.inl (state.resultSeparate i index same))

#print axioms ScalarCarryState.advance

end UInt256Proof.Safety
