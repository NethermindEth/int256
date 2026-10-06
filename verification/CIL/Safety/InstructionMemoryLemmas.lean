import CIL.Safety.InstructionMemory

namespace CIL.Safety

theorem instructions_append (first second : List CIL.Op) (stack : List Value) (m : Memory) :
    instructions (first ++ second) stack m =
      (instructions first stack m).bind (fun (memory, values) => instructions second values memory) := by
  induction first generalizing stack m with
  | nil => rfl
  | cons op first ih =>
    simp only [List.cons_append, instructions]
    cases hi : instruction op stack m with
    | error fault => rfl
    | ok result =>
      rcases result with ⟨memory, values⟩
      exact ih values memory

theorem instruction_fault_cannot_be_erased (first second : List CIL.Op) (stack : List Value)
    (m : Memory) (fault : ExecutionFault) (h : instructions first stack m = .error fault) :
    instructions (first ++ second) stack m = .error fault := by
  rw [instructions_append, h]
  rfl

theorem successful_instruction_prefix (first second : List CIL.Op) (stack : List Value)
    (m final : Memory) (values : List Value)
    (h : instructions (first ++ second) stack m = .ok (final, values)) :
    ∃ intermediate stack', instructions first stack m = .ok (intermediate, stack') := by
  rw [instructions_append] at h
  cases hi : instructions first stack m with
  | error fault => simp [hi, Except.bind] at h
  | ok result =>
    rcases result with ⟨memory, stack'⟩
    exact ⟨memory, stack', rfl⟩

theorem checked_write_preserves_wellFormed (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) (reference : ManagedReference) (width : Nat)
    (hm : m.WellFormed)
    (h : checkedAt reference width (write m r bytes alignment) = .ok result) :
    result.WellFormed := by
  cases hw : write m r bytes alignment <;> simp only [hw, checkedAt, Except.mapError] at h
  · cases h
  · cases h
    exact write_preserves_wellFormed _ _ _ _ _ hm hw

theorem storeValue_preserves_wellFormed (m result : Memory) (reference : ManagedReference)
    (value : CIL.Value) (hm : m.WellFormed)
    (h : storeValue m reference value = .ok result) : result.WellFormed := by
  unfold storeValue at h
  split at h <;> try cases h
  all_goals
    cases reference with
    | null => cases h
    | address address =>
      simp only [referenceAt, Bind.bind, Except.bind] at h
      exact checked_write_preserves_wellFormed _ _ _ _ _ _ _ hm h

#print axioms storeValue_preserves_wellFormed

theorem memoryInstruction_preserves_wellFormed (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed)
    (h : memoryInstruction operation stack m = .ok (result, values)) : result.WellFormed := by
  unfold memoryInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact hm
      | solve | apply storeValue_preserves_wellFormed _ _ _ _ hm; assumption
      | cases h
      | split at h

#print axioms memoryInstruction_preserves_wellFormed

theorem instruction_preserves_wellFormed (operation : CIL.Op) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed)
    (h : instruction operation stack m = .ok (result, values)) : result.WellFormed := by
  unfold instruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact hm
      | solve | apply memoryInstruction_preserves_wellFormed _ _ _ _ _ hm; assumption
      | solve | apply storeValue_preserves_wellFormed _ _ _ _ hm; assumption
      | cases h
      | split at h

#print axioms instruction_preserves_wellFormed

end CIL.Safety
