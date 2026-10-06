import UInt256.Methods.Subtract.BorrowCaller

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety

/-- Mathematical borrow recurrence over the four initial operand limbs. -/
def scalarBorrowValue (memory : CIL.Safety.Memory) (left right : Reference) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => if h : n < 4 then
      UInt256Proof.borrow (inputLimb memory left ⟨n, h⟩) (inputLimb memory right ⟨n, h⟩)
        (scalarBorrowValue memory left right n)
    else 0

structure ScalarBorrowState (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference) (done : Nat) (borrowIndex : Nat := 1) (resultBase : Nat := 2) : Prop where
  call : CallingConditions Extracted.program current [left, right] [output]
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

/-- A checked borrow invocation advances the same parent invariant, retaining
    initial operand snapshots and every previously completed result home. -/
theorem ScalarBorrowState.advance {original before after : CIL.Safety.Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} {borrowIndex resultBase : Nat} (index : Fin 4)
    (state : ScalarBorrowState original before frame left right output borrowHome results index.val borrowIndex resultBase)
    (math : BorrowPost (inputLimb original left index) (inputLimb original right index)
      (scalarBorrowValue original left right index.val) borrowHome (results index) before after) :
    ScalarBorrowState original after frame left right output borrowHome results (index.val + 1) borrowIndex resultBase := by
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
    exact (math.private_input_bytes reference (separate reference member).1
      (separate reference member).2).trans (state.inputBytes reference member)
  · simpa only [scalarBorrowValue, dite_eq_left index.isLt] using math.borrowBytes
  · simpa only [scalarBorrowValue, dite_eq_left index.isLt] using math.borrowBound
  · intro id old offset
    have belowBorrow := Nat.lt_of_lt_of_le old state.borrowFresh
    have belowResult := Nat.lt_of_lt_of_le old (state.resultsFresh index)
    exact (math.footprint id offset
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
      exact math.footprint _ _ (Or.inl (state.borrowSeparate i))
        (Or.inl (state.resultSeparate i index same))

#print axioms ScalarBorrowState.advance

end UInt256Proof.Subtract.Safety
