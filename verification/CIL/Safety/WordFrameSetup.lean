import CIL.Safety.WordHomes

namespace CIL.Safety

/-- Checked numeric/root initializer metadata suffices to construct private
    homes. The body and its recipe are parameters, independent of extraction. -/
theorem word_frame_setup (body : CIL.Method) (specs : List (Option (BitVec 64)))
    (kinds : body.localKinds = wordKinds specs) (initializers : body.locals = wordInitializers specs)
    (arguments : body.aggregateArgs = []) (memory : Memory) (args : List Value)
    (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame body args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity specs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨slots, owned, result, made, homes⟩ := make_word_locals memory memory.nextIdentity specs wellFormed
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have setup : enterFrame body args memory = .ok (frame, result) := by
    simp only [enterFrame, kinds, initializers, made, arguments, makeArgumentHomes,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]
    rfl
  exact ⟨frame, result, setup, homes, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
    enterFrame_preserves_wellFormed _ _ _ _ _ wellFormed setup⟩

#print axioms word_frame_setup
end CIL.Safety
