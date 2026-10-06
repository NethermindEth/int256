import CIL.Safety.ExecutionLifetime
import CIL.Safety.FrameAllocations

namespace CIL.Safety

/-- Calls and returns keep the current frame until the run dispatcher acts;
    ordinary steps and constructor allocation supply their updated frame. -/
def FrameAction.frameAfter (action : FrameAction) (current : Frame) : Frame :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ => frame
  | .call _ _ _ _ | .returned _ _ => current

theorem step_preserves_frame_allocations (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned)
    (h : step body operation pc args frame stack m = .ok action) :
    FrameAllocations action.memory (action.frameAfter frame).activation
      (action.frameAfter frame).owned := by
  have ext := step_extends_allocations _ _ _ _ _ _ _ _ h
  have bounds : ∀ id ∈ frame.owned, id < m.nextIdentity := by
    intro id member
    obtain ⟨a, present, _, _⟩ := owns id member
    exact (hm.1 _ _ present).1
  have retained := owns.preserve ext bounds
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact retained
      | solve |
          change FrameAllocations _ frame.activation (_ :: frame.owned)
          have allocated := allocateHome_owned _ _ _ _ _ (by assumption)
          have fresh := allocateHome_fresh _ _ _ _ _ (by assumption)
          have new := allocated.preserve (storeValue_extends_allocations _ _ _ _ (by assumption))
            (by
              intro id member
              simp only [List.mem_singleton] at member
              subst id
              exact fresh.2.2)
          intro id member
          rcases List.mem_cons.mp member with rfl | member
          · exact new _ (by simp)
          · exact retained id member
      | cases h
      | split at h

theorem child_run_preserves_parent_frame (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (args values : List Value) (child parent : Frame)
    (m entered final : Memory) (hm : m.WellFormed)
    (owns : FrameAllocations m parent.activation parent.owned)
    (setup : enterFrame body args m = .ok (child, entered))
    (finish : run program fuel method 0 args child [] entered = .ok (final, values)) :
    FrameAllocations final parent.activation parent.owned := by
  apply owns.preserve (entered_run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ setup finish)
  intro id member
  obtain ⟨a, present, _, _⟩ := owns id member
  exact (hm.1 _ _ present).1

#print axioms step_preserves_frame_allocations
#print axioms child_run_preserves_parent_frame

end CIL.Safety
