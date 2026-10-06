import CIL.Safety.LiveValues

namespace CIL.Safety

theorem loadValue_scalar_valid (m : Memory) (r : ManagedReference) (width : Nat)
    (value : CIL.Value) (h : loadValue m r width = .ok value) : (Value.scalar value).Valid m := by
  unfold loadValue at h
  repeat' first
    | rfl
    | cases h
    | split at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem add_result_valid (m : Memory) (r result : Reference) (size : Nat) (offset : BitVec 64)
    (h : add m r size offset = .ok result) : form m result = .ok result := by
  unfold add at h
  cases hf : form m r <;> simp only [hf, Bind.bind, Except.bind] at h
  · cases h
  · have same := form_returns_input _ _ _ h
    rw [← same] at h
    exact h

theorem checked_add_result_valid (m : Memory) (r result : Reference) (size : Nat)
    (offset : BitVec 64) (reference : ManagedReference) (width : Nat)
    (h : checkedAt reference width (add m r size offset) = .ok result) :
    form m result = .ok result := by
  cases ha : add m r size offset <;> simp only [ha, checkedAt, Except.mapError] at h
  · cases h
  · cases h
    exact add_result_valid _ _ _ _ _ ha

theorem memoryInstruction_values_valid (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed) (valid : ValuesValid m stack)
    (h : memoryInstruction operation stack m = .ok (result, values)) : ValuesValid result values := by
  have retained := valid.preserve hm (memoryInstruction_extends_allocations _ _ _ _ _ h)
  unfold memoryInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact retained
      | exact retained.head
      | exact retained.tail
      | exact retained.tail.tail
      | solve |
          apply ValuesValid.cons
          · first
            | rfl
            | exact retained.head
            | solve | apply loadValue_scalar_valid; assumption
            | solve | apply formValue_result_valid; assumption
            | solve | apply checked_add_result_valid; assumption
          · first | exact retained | exact retained.tail | exact retained.tail.tail
      | cases h
      | split at h

theorem instruction_values_valid (operation : CIL.Op) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed) (valid : ValuesValid m stack)
    (h : instruction operation stack m = .ok (result, values)) : ValuesValid result values := by
  have retained := valid.preserve hm (instruction_extends_allocations _ _ _ _ _ h)
  unfold instruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact retained
      | exact retained.head
      | exact retained.tail
      | exact retained.tail.tail
      | solve |
          apply ValuesValid.cons
          · first
            | rfl
            | exact retained.head
            | solve | apply loadValue_scalar_valid; assumption
            | solve | apply formValue_result_valid; assumption
            | solve | apply checked_add_result_valid; assumption
          · first | exact retained | exact retained.tail | exact retained.tail.tail
      | solve | apply memoryInstruction_values_valid _ _ _ _ _ hm valid; assumption
      | cases h
      | split at h

#print axioms loadValue_scalar_valid
#print axioms checked_add_result_valid
#print axioms memoryInstruction_values_valid
#print axioms instruction_values_valid

end CIL.Safety
