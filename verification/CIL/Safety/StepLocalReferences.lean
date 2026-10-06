import CIL.Safety.LocalReferences
import CIL.Safety.ExecutionFrameOwnership

namespace CIL.Safety

theorem stored_frame_references_valid (m result : Memory) (frame : Frame) (index : Nat)
    (slot final : LocalSlot) (value : Value) (hm : m.WellFormed)
    (valid : frame.ReferencesValid m) (present : frame.locals[index]? = some slot)
    (h : storeLocal m slot value = .ok (final, result)) :
    Frame.ReferencesValid result { frame with locals := frame.locals.set index final } := by
  have retained := valid.preserve hm (storeLocal_extends_allocations _ _ _ _ _ h)
  have stored := storeLocal_preserves_reference_validity _ _ _ _ _ hm
    (valid.1 slot (List.mem_of_getElem? present)) h
  refine ⟨?_, retained.2⟩
  intro other member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact retained.1 other old
  · subst other
    exact stored

theorem step_preserves_frame_references (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed) (valid : frame.ReferencesValid m)
    (h : step body operation pc args frame stack m = .ok action) :
    (action.frameAfter frame).ReferencesValid action.memory := by
  have retained := valid.preserve hm (step_extends_allocations _ _ _ _ _ _ _ _ h)
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact retained
      | solve |
          apply stored_frame_references_valid
          · exact hm
          · exact valid
          · assumption
          · assumption
      | cases h
      | split at h

#print axioms stored_frame_references_valid
#print axioms step_preserves_frame_references

end CIL.Safety
