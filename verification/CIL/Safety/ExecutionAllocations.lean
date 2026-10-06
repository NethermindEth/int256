import CIL.Safety.ExecutionInvariants
import CIL.Safety.FrameOwnership

namespace CIL.Safety

theorem checked_write_extends_allocations (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) (reference : ManagedReference) (width : Nat)
    (h : checkedAt reference width (write m r bytes alignment) = .ok result) :
    AllocationExtension m result := by
  cases hw : write m r bytes alignment <;> simp only [hw, checkedAt, Except.mapError] at h
  · cases h
  · cases h
    exact write_extends_allocations _ _ _ _ _ hw

theorem storeValue_extends_allocations (m result : Memory) (reference : ManagedReference)
    (value : CIL.Value) (h : storeValue m reference value = .ok result) :
    AllocationExtension m result := by
  unfold storeValue at h
  split at h <;> try cases h
  all_goals
    cases reference with
    | null => cases h
    | address address =>
      simp only [referenceAt, Bind.bind, Except.bind] at h
      exact checked_write_extends_allocations _ _ _ _ _ _ _ h

theorem memoryInstruction_extends_allocations (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory)
    (h : memoryInstruction operation stack m = .ok (result, values)) :
    AllocationExtension m result := by
  unfold memoryInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .refl m
      | solve | apply storeValue_extends_allocations; assumption
      | cases h
      | split at h

theorem instruction_extends_allocations (operation : CIL.Op) (stack values : List Value)
    (m result : Memory) (h : instruction operation stack m = .ok (result, values)) :
    AllocationExtension m result := by
  unfold instruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .refl m
      | solve | apply memoryInstruction_extends_allocations; assumption
      | solve | apply storeValue_extends_allocations; assumption
      | cases h
      | split at h

theorem staticReference_extends_allocations (descriptor : CIL.StaticDescriptor)
    (m result : Memory) (reference : Reference)
    (h : staticReference descriptor m = .ok (result, reference)) :
    AllocationExtension m result := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨name, cached⟩ := binding
    obtain ⟨rfl, _, _⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact .refl _
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
      have ext := allocate_extends_allocations _ _ _ _ ha
      exact ⟨ext.next, ext.lookup⟩

theorem staticInstruction_extends_allocations (body : CIL.Method) (pc : Nat)
    (operation : CIL.MemoryOp) (stack values : List Value) (m result : Memory)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    AllocationExtension m result := by
  unfold staticInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .refl m
      | solve | apply staticReference_extends_allocations; assumption
      | solve | apply memoryInstruction_extends_allocations; assumption
      | cases h
      | split at h

theorem step_extends_allocations (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    AllocationExtension m action.memory := by
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact .refl m
      | solve | apply storeLocal_extends_allocations; assumption
      | solve | apply staticInstruction_extends_allocations; assumption
      | solve | apply instruction_extends_allocations; assumption
      | solve |
          apply AllocationExtension.trans
          · exact (allocateHome_fresh _ _ _ _ _ (by assumption)).1
          · apply storeValue_extends_allocations; assumption
      | cases h
      | split at h

/-- Frame teardown changes lifetime flags, but never recycles an identity. -/
theorem leaveFrame_nextIdentity (frame : Frame) (m : Memory) :
    (leaveFrame frame m).nextIdentity = m.nextIdentity :=
  (expireAll_retained_fields frame.owned m).2.2.2

#print axioms step_extends_allocations

def Frame.OwnedAbove (frame : Frame) (watermark : Nat) : Prop :=
  ∀ id ∈ frame.owned, watermark ≤ id

def FrameAction.OwnedAbove (action : FrameAction) (watermark : Nat) : Prop :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ => frame.OwnedAbove watermark
  | .call _ _ _ _ | .returned _ _ => True

theorem step_ownedAbove (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (watermark : Nat) (old : frame.OwnedAbove watermark)
    (bound : watermark ≤ m.nextIdentity)
    (h : step body operation pc args frame stack m = .ok action) :
    action.OwnedAbove watermark := by
  unfold step at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | exact old
      | exact True.intro
      | solve |
          change ∀ id ∈ _ :: frame.owned, watermark ≤ id
          intro id member
          rcases List.mem_cons.mp member with rfl | member
          · have fresh := allocateHome_fresh _ _ _ _ _ (by assumption)
            rw [fresh.2.1]
            exact bound
          · exact old id member
      | cases h
      | split at h

#print axioms step_ownedAbove

end CIL.Safety
