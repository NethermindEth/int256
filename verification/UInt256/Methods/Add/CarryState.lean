import UInt256.Methods.Add.CarryCaller

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
