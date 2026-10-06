import CIL.Safety.WordMemory
import CIL.Safety.HomeProgress
import CIL.Safety.FrameMemoryBelow

namespace CIL.Safety

/-- A fresh initialized word local has exact readback and preserves older memory. -/
theorem make_local_word64 (memory : Memory) (activation : Nat) (word : BitVec 64)
    (wellFormed : memory.WellFormed) :
    ∃ reference result,
      makeLocal activation .word64 (.i64 word) memory =
        .ok (.bytes .word64 reference, [reference.allocation], result) ∧
      read result reference 8 1 = .ok (numberBytes word.toNat 8) ∧
      access result reference 8 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨reference, allocated, home⟩ := allocateHome_succeeds memory activation 8 wellFormed (by decide)
  have ready := allocateHome_write_access _ _ _ _ _ home
  obtain ⟨result, written, stored, readback, _⟩ := store_local_word64 word ready.access
  have created : makeLocal activation .word64 (.i64 word) memory =
      .ok (.bytes .word64 reference, [reference.allocation], result) := by
    simp [makeLocal, localWidth, home, stored, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨reference, result, created, readback, (ready.after_write written).access,
    makeLocal_preserves_caller_memory _ _ _ _ _ _ _ created⟩

theorem step_load_word64 {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference} {word : BitVec 64}
    (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (loaded : read memory reference 8 1 = .ok (numberBytes word.toNat 8)) :
    step body (.local index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar (.i64 word) :: stack) frame memory) := by
  simp only [step, slot, load_local_word64_of_read loaded, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

theorem step_store_word64 {body : CIL.Method} {pc index : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference} (word : BitVec 64)
    (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (ready : access memory reference 8 1 true = .ok ()) :
    ∃ result,
      step body (.setLocal index) pc args frame (.scalar (.i64 word) :: rest) memory =
        .ok (.next (pc + 1) rest
          { frame with locals := frame.locals.set index (.bytes .word64 reference) } result) ∧
      write memory reference (numberBytes word.toNat 8) 1 = .ok result ∧
      read result reference 8 1 = .ok (numberBytes word.toNat 8) := by
  obtain ⟨result, written, stored, readback, _⟩ := store_local_word64 word ready
  refine ⟨result, ?_, written, readback⟩
  simp only [step, slot, stored, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Storing a numeric local changes its bytes, not the frame's slot identities.
    This lets subsequent calls retain indexed home and separation facts. -/
theorem step_store_word64_same_frame {body : CIL.Method} {pc index : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference} (word : BitVec 64)
    (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (ready : access memory reference 8 1 true = .ok ()) :
    ∃ result,
      step body (.setLocal index) pc args frame (.scalar (.i64 word) :: rest) memory =
        .ok (.next (pc + 1) rest frame result) ∧
      write memory reference (numberBytes word.toNat 8) 1 = .ok result ∧
      read result reference 8 1 = .ok (numberBytes word.toNat 8) := by
  obtain ⟨result, stepped, written, loaded⟩ :=
    step_store_word64 (body := body) (pc := pc) (args := args) (rest := rest) word slot ready
  have unchanged : frame.locals.set index (.bytes .word64 reference) = frame.locals := by
    apply List.ext_getElem?
    intro other
    by_cases same : index = other
    · subst other
      simp only [List.getElem?_set_self', slot]
      rfl
    · simp only [List.getElem?_set_ne same]
  refine ⟨result, ?_, written, loaded⟩
  simpa only [unchanged] using stepped

#print axioms step_store_word64_same_frame
#print axioms make_local_word64
#print axioms step_load_word64
#print axioms step_store_word64

end CIL.Safety
