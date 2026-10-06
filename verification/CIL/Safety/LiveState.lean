import CIL.Safety.LocalReferences
import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.ReturnReferences

namespace CIL.Safety

/-- Reference/storage invariants at a CIL boundary. This deliberately permits
    uninitialized local/output bytes. Method proofs must still establish every
    read's initialization and access obligations, plus absence of faults. -/
structure LiveState (program : CIL.Program) (args : List Value) (frame : Frame)
    (stack : List Value) (m : Memory) : Prop where
  memory : m.WellFormed
  arguments : ValuesValid m args
  stack : ValuesValid m stack
  references : frame.ReferencesValid m
  owned : FrameAllocations m frame.activation frame.owned
  statics : StaticWorldValid (programStaticDescriptors program) m

theorem enterFrame_live_state (program : CIL.Program) (body : CIL.Method) (args : List Value)
    (m result : Memory) (frame : Frame) (hm : m.WellFormed) (valid : ValuesValid m args)
    (world : StaticWorldValid (programStaticDescriptors program) m)
    (h : enterFrame body args m = .ok (frame, result)) : LiveState program args frame [] result := by
  exact ⟨enterFrame_preserves_wellFormed _ _ _ _ _ hm h,
    valid.preserve hm (enterFrame_fresh _ _ _ _ _ h).1,
    by simp [ValuesValid], enterFrame_references_valid _ _ _ _ _ hm h,
    enterFrame_owned _ _ _ _ _ h, enterFrame_preserves_static_world _ _ _ _ _ _ hm world h⟩

/-- Establish the entry invariant from the actual checked argument list and
    frame preparation, without assuming the body's future execution succeeds. -/
theorem checked_entry_live_state (program : CIL.Program) (body : CIL.Method)
    (args checked : List Value) (m result : Memory) (frame : Frame) (hm : m.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) m)
    (check : args.mapM (checkedValue m) = .ok checked)
    (enter : enterFrame body checked m = .ok (frame, result)) :
    LiveState program checked frame [] result :=
  enterFrame_live_state _ _ _ _ _ _ hm (checkedValues_valid _ _ _ check).2 world enter

/-- A successful child preserves the parent's existing roots and values.
    Child return values and the resumed stack are checked separately. -/
theorem child_preserves_parent_state (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (childArgs values args stack : List Value) (child parent : Frame)
    (m entered final : Memory) (state : LiveState program args parent stack m)
    (setup : enterFrame body childArgs m = .ok (child, entered))
    (finish : run program fuel method 0 childArgs child [] entered = .ok (final, values)) :
    LiveState program args parent stack final := by
  have ext := entered_run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ setup finish
  have childWF := enterFrame_preserves_wellFormed _ _ _ _ _ state.memory setup
  have childWorld := enterFrame_preserves_static_world _ _ _ _ _ _ state.memory state.statics setup
  exact ⟨run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ childWF finish,
    state.arguments.preserve state.memory ext, state.stack.preserve state.memory ext,
    state.references.preserve state.memory ext,
    child_run_preserves_parent_frame _ _ _ _ _ _ _ _ _ _ _ state.memory state.owned setup finish,
    run_preserves_static_world _ _ _ _ _ _ _ _ _ _ childWF
      (enterFrame_owned _ _ _ _ _ setup) childWorld finish⟩

theorem child_resume_live_state (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (childArgs values args rest : List Value) (child parent : Frame)
    (m entered final : Memory) (state : LiveState program args parent rest m)
    (setup : enterFrame body childArgs m = .ok (child, entered))
    (finish : run program fuel method 0 childArgs child [] entered = .ok (final, values)) :
    LiveState program args parent (values ++ rest) final := by
  have preserved := child_preserves_parent_state _ _ _ _ _ _ _ _ _ _ _ _ _ state setup finish
  exact { preserved with stack := (run_result_valid _ _ _ _ _ _ _ _ _ _ finish).append preserved.stack }

#print axioms enterFrame_live_state
#print axioms checked_entry_live_state
#print axioms child_preserves_parent_state
#print axioms child_resume_live_state

end CIL.Safety
