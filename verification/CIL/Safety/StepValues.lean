import CIL.Safety.StaticReferences
import CIL.Safety.LocalReferences

namespace CIL.Safety

theorem ValuesValid.drop {m : Memory} {values : List Value}
    (valid : ValuesValid m values) (count : Nat) : ValuesValid m (values.drop count) :=
  fun _ member => valid _ (List.mem_of_mem_drop member)

theorem checkedValues_preserved (m result : Memory) (values checked : List Value)
    (hm : m.WellFormed) (ext : AllocationExtension m result)
    (h : values.mapM (checkedValue m) = .ok checked) : ValuesValid result checked :=
  (checkedValues_valid _ _ _ h).2.preserve hm ext

theorem allocated_store_reference_valid (m home result : Memory) (activation width : Nat)
    (r : Reference) (value : CIL.Value) (hm : m.WellFormed)
    (allocation : allocateHome m activation width = .ok (r, home))
    (store : storeValue home (.address r) value = .ok result) : form result r = .ok r :=
  (storeValue_extends_allocations _ _ _ _ store).preserves_reference
    (allocateHome_preserves_wellFormed _ _ _ _ _ hm allocation) r r
    (allocateHome_reference_valid _ _ _ _ _ allocation)

def FrameAction.LiveValues (action : FrameAction) : Prop :=
  match action with
  | .next _ values _ memory | .returned values memory => ValuesValid memory values
  | .call _ args rest memory | .construct _ args rest _ _ memory =>
    ValuesValid memory args ∧ ValuesValid memory rest

theorem step_values_valid (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed) (valid : ValuesValid m stack)
    (h : step body operation pc args frame stack m = .ok action) : action.LiveValues := by
  have ext := step_extends_allocations _ _ _ _ _ _ _ _ h
  have retained := valid.preserve hm ext
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact retained
      | exact retained.tail
      | solve | exact retained.drop _
      | solve | apply checkedValues_preserved _ _ _ _ hm ext; assumption
      | solve | apply staticInstruction_values_valid _ _ _ _ _ _ _ hm valid; assumption
      | solve | apply instruction_values_valid _ _ _ _ _ hm valid; assumption
      | solve |
          apply ValuesValid.append
          · apply checkedValues_preserved _ _ _ _ hm ext; assumption
          · exact retained.drop _
      | solve |
          apply ValuesValid.cons
          · first
            | solve | exact (checkedValue_valid _ _ _ (by assumption)).2
            | solve | apply loadLocal_result_valid; assumption
            | solve | apply localAddress_result_valid; assumption
            | solve | apply allocated_store_reference_valid; exact hm; assumption; assumption
          · first
            | exact retained
            | solve | apply checkedValues_preserved _ _ _ _ hm ext; assumption
      | constructor
      | cases h
      | split at h

#print axioms allocated_store_reference_valid
#print axioms step_values_valid

end CIL.Safety
