import CIL.Safety.StaticMemory
import CIL.Safety.InstructionMemoryLemmas
namespace CIL.Safety
theorem cached_static_reference_checked (descriptor : CIL.StaticDescriptor) (m final : Memory)
    (name : Nat) (reference result : Reference)
    (cache : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) = some (name, reference))
    (success : staticReference descriptor m = .ok (final, result)) :
    final = m ∧ result = reference ∧ read m reference descriptor.bytes.length 1 = .ok descriptor.bytes := by
  simp only [staticReference, cache] at success
  cases hl : liveAllocation m reference.allocation with
  | error fault => simp [hl, checkedAt, Except.mapError, Bind.bind, Except.bind] at success
  | ok allocation =>
    simp only [hl, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at success
    split at success
    · cases hr : read m reference descriptor.bytes.length 1 with
      | error fault => simp [hr] at success
      | ok bytes =>
        simp only [hr] at success
        split at success
        · simp only [Except.ok.injEq, Prod.mk.injEq] at success
          have he : bytes = descriptor.bytes := by simpa using (by assumption : (bytes == descriptor.bytes) = true)
          exact ⟨success.1.symm, success.2.symm, congrArg Except.ok he⟩
        · cases success
    · cases success
#print axioms cached_static_reference_checked
theorem staticReference_preserves_wellFormed (descriptor : CIL.StaticDescriptor)
    (m result : Memory) (reference : Reference) (hm : m.WellFormed)
    (h : staticReference descriptor m = .ok (result, reference)) : result.WellFormed := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨name, cached⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact hm
  | none =>
    simp only [staticReference, hc] at h
    cases ha : allocate m ⟨.immutableStatic, ⟨descriptor.bytes.length, 1, []⟩,
        true, [descriptor.bytes.length]⟩ <;>
      simp only [ha, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i allocated
      obtain ⟨id, memory⟩ := allocated
      cases h
      have hw := allocate_preserves_wellFormed _ _ _ _ hm ha
      refine ⟨hw.1, ?_⟩
      intro view hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · have lookup := allocation_lookup m _ id memory ha
        exact ⟨_, lookup, by simp⟩
      · exact hw.2 view hv

#print axioms staticReference_preserves_wellFormed

theorem staticInstruction_preserves_wellFormed (body : CIL.Method) (pc : Nat)
    (operation : CIL.MemoryOp) (stack values : List Value) (m result : Memory)
    (hm : m.WellFormed)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) : result.WellFormed := by
  unfold staticInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact hm
      | solve | apply staticReference_preserves_wellFormed _ _ _ _ hm; assumption
      | solve | apply memoryInstruction_preserves_wellFormed _ _ _ _ _ hm; assumption
      | cases h
      | split at h

#print axioms staticInstruction_preserves_wellFormed

end CIL.Safety
