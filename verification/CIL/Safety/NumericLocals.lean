import CIL.Safety.NumericLocalLoad
import CIL.Safety.HomeProgress
import CIL.Safety.FrameMemoryBelow

namespace CIL.Safety

/-- Fresh typed numeric storage has initialized readback and preserves older memory. -/
theorem make_numeric_local (memory : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (wellFormed : memory.WellFormed) (fits : localNumber kind value = .ok number) :
    ∃ reference result,
      makeLocal activation kind value memory =
        .ok (.bytes kind reference, [reference.allocation], result) ∧
      read result reference (localWidth kind) 1 = .ok (numberBytes number (localWidth kind)) ∧
      access result reference (localWidth kind) 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result := by
  have numeric : kind ≠ .reference := by
    cases kind <;> cases value <;> simp_all [localNumber]
  have modeled : value ≠ .unmodeled := by
    cases kind <;> cases value <;> simp_all [localNumber]
  have bounded : localWidth kind < nativeLimit := by cases kind <;> decide
  obtain ⟨reference, allocated, home⟩ := allocateHome_succeeds memory activation (localWidth kind) wellFormed bounded
  have ready := allocateHome_write_access _ _ _ _ _ home
  obtain ⟨result, written, stored, readback⟩ := store_numeric_local kind value number fits ready.access
  have created : makeLocal activation kind value memory =
      .ok (.bytes kind reference, [reference.allocation], result) := by
    cases kind <;> simp_all [makeLocal, home, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨reference, result, created, readback, (ready.after_write written).access,
    makeLocal_preserves_caller_memory _ _ _ _ _ _ _ created⟩

theorem step_load_numeric_local {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (slot : frame.locals[index]? = some (.bytes kind reference))
    (loaded : read memory reference (localWidth kind) 1 = .ok (numberBytes number (localWidth kind))) :
    step body (.local index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar value :: stack) frame memory) := by
  simp only [step, slot, load_numeric_local kind value number fits loaded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem step_store_numeric_local {body : CIL.Method} {pc index : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (slot : frame.locals[index]? = some (.bytes kind reference))
    (ready : access memory reference (localWidth kind) 1 true = .ok ()) :
    ∃ result,
      step body (.setLocal index) pc args frame (.scalar value :: rest) memory =
        .ok (.next (pc + 1) rest frame result) ∧
      write memory reference (numberBytes number (localWidth kind)) 1 = .ok result ∧
      read result reference (localWidth kind) 1 = .ok (numberBytes number (localWidth kind)) := by
  obtain ⟨result, written, stored, readback⟩ := store_numeric_local kind value number fits ready
  have unchanged : frame.locals.set index (.bytes kind reference) = frame.locals := by
    apply List.ext_getElem?
    intro other
    by_cases same : index = other
    · subst other
      simp only [List.getElem?_set_self', slot]
      rfl
    · simp only [List.getElem?_set_ne same]
  refine ⟨result, ?_, written, readback⟩
  simp only [step, slot, stored, unchanged, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms make_numeric_local
#print axioms step_load_numeric_local
#print axioms step_store_numeric_local
end CIL.Safety
