import UInt256.Safety.Calling

namespace UInt256Model.Safety

open CIL.Safety

/-- Caller storage may contain several words and unrelated bytes. Equal
    identities mean shared storage; distinct identities mean distinct objects. -/
structure CallerLayout where
  extent : Nat
  identities : Nat
  left : Reference
  right : Reference
  output : Reference

def CallerLayout.Valid (layout : CallerLayout) : Prop :=
  layout.extent < nativeLimit ∧
    (∀ reference ∈ [layout.left, layout.right, layout.output],
      reference.allocation < layout.identities ∧ reference.offset + 32 ≤ layout.extent)

def callerAllocation (size : Nat) : Allocation :=
  { kind := .managedHeap, layout := ⟨size, 1, []⟩ }

def callerView (reference : Reference) (writing : Bool) : View :=
  ⟨reference.allocation, reference.offset, 32, !writing, writing⟩

def inputByte (layout : CallerLayout) (id offset : Nat) : Prop :=
  (id = layout.left.allocation ∧ layout.left.offset ≤ offset ∧ offset < layout.left.offset + 32) ∨
  (id = layout.right.allocation ∧ layout.right.offset ≤ offset ∧ offset < layout.right.offset + 32)

instance (layout : CallerLayout) (id offset : Nat) : Decidable (inputByte layout id offset) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Arbitrary shared byte contents, with exactly the two inputs initialized.
    Output authority is independent of initialization and read authority. -/
def callerMemory (layout : CallerLayout) (bytes : Nat → Nat → BitVec 8) : CIL.Safety.Memory :=
  { allocations := fun id => if id < layout.identities then some (callerAllocation layout.extent) else none
    cells := fun id offset => ⟨bytes id offset, decide (inputByte layout id offset)⟩
    views := [callerView layout.left false, callerView layout.right false, callerView layout.output true]
    nextIdentity := layout.identities }

theorem callerMemory_wellFormed (layout : CallerLayout) (valid : layout.Valid)
    (bytes : Nat → Nat → BitVec 8) : (callerMemory layout bytes).WellFormed := by
  constructor
  · intro id allocation present
    simp only [callerMemory] at present
    split at present
    · rename_i bound
      cases present
      exact ⟨bound, by simp [Allocation.WellFormed, callerAllocation, valid.1]⟩
    · cases present
  · intro view member
    simp only [callerMemory, List.mem_cons, List.not_mem_nil, or_false] at member
    have bounds : view.allocation < layout.identities ∧ view.start + view.length ≤ layout.extent := by
      rcases member with rfl | rfl | rfl
      all_goals first
        | exact valid.2 layout.left (by simp)
        | exact valid.2 layout.right (by simp)
        | exact valid.2 layout.output (by simp)
    exact ⟨callerAllocation layout.extent, by simp [callerMemory, bounds.1], bounds.2⟩

theorem callerMemory_access (layout : CallerLayout) (valid : layout.Valid)
    (bytes : Nat → Nat → BitVec 8) (reference : Reference) (writing : Bool)
    (bounds : reference.allocation < layout.identities ∧ reference.offset + 32 ≤ layout.extent)
    (member : callerView reference writing ∈ (callerMemory layout bytes).views) :
    AccessRequirements (callerMemory layout bytes) reference 32 1 writing
      (callerAllocation layout.extent) := by
  refine ⟨?_, rfl, ?_, ?_, bounds.2, by simp [callerAllocation, Nat.mod_one], ?_, ?_⟩
  · simp [callerMemory, bounds.1]
  · have interior : reference.offset < layout.extent := by omega
    have native : reference.offset < nativeLimit := Nat.lt_trans interior valid.1
    simp [validPosition, callerAllocation, interior, native]
  · simp [callerAllocation]
  · simp [callerAllocation]
  · intro i bound
    apply permitted_by_view (view := callerView reference writing) member
    · rfl
    · exact Nat.le_add_right _ _
    · change reference.offset + i < reference.offset + 32
      omega
    · cases writing <;> rfl

theorem callerMemory_calling (program : CIL.Program) (layout : CallerLayout)
    (valid : layout.Valid) (bytes : Nat → Nat → BitVec 8)
    (sizes : ∀ descriptor ∈ programStaticDescriptors program, descriptor.bytes.length < nativeLimit)
    (identities : ∀ left ∈ programStaticDescriptors program,
      ∀ right ∈ programStaticDescriptors program, left.identity = right.identity → left = right) :
    CallingConditions program (callerMemory layout bytes) [layout.left, layout.right] [layout.output] := by
  apply CallingConditions.of_requirements (callerMemory_wellFormed layout valid bytes)
    (empty_static_world_valid _ _ sizes identities rfl)
  · intro reference member
    have included : reference ∈ [layout.left, layout.right, layout.output] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl <;> simp
    refine ⟨callerAllocation layout.extent,
      callerMemory_access layout valid bytes reference false (valid.2 reference included) ?_, ?_⟩
    · simp only [callerMemory, List.mem_cons, List.not_mem_nil, or_false]
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (congrArg (fun r => callerView r false) (List.mem_singleton.mp member)))
    · intro i bound
      have first : reference.offset ≤ reference.offset + i := Nat.le_add_right _ _
      have last : reference.offset + i < reference.offset + 32 := by omega
      rcases List.mem_cons.mp member with rfl | member
      · simp [callerMemory, inputByte, first, last]
      · have same := List.mem_singleton.mp member
        subst reference
        simp [callerMemory, inputByte, first, last]
  · intro reference member
    have same := List.mem_singleton.mp member
    subst reference
    exact ⟨_, callerMemory_access layout valid bytes layout.output true
      (valid.2 _ (by simp)) (by simp [callerMemory])⟩

theorem callerMemory_unknown_outside_inputs (layout : CallerLayout) (bytes : Nat → Nat → BitVec 8)
    (id offset : Nat) (outside : ¬ inputByte layout id offset) :
    ((callerMemory layout bytes).cells id offset).initialized = false := by
  simp [callerMemory, outside]

def disjointLayout : CallerLayout := ⟨32, 3, ⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩⟩
def exactAliasLayout : CallerLayout := ⟨32, 1, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
def partialOverlapLayout : CallerLayout := ⟨80, 1, ⟨0, 0⟩, ⟨0, 16⟩, ⟨0, 40⟩⟩

theorem caller_layouts_valid :
    disjointLayout.Valid ∧ exactAliasLayout.Valid ∧ partialOverlapLayout.Valid := by
  simp [CallerLayout.Valid, disjointLayout, exactAliasLayout, partialOverlapLayout, nativeLimit]

theorem caller_examples_nonvacuous (program : CIL.Program) (bytes : Nat → Nat → BitVec 8)
    (sizes : ∀ descriptor ∈ programStaticDescriptors program, descriptor.bytes.length < nativeLimit)
    (identities : ∀ left ∈ programStaticDescriptors program,
      ∀ right ∈ programStaticDescriptors program, left.identity = right.identity → left = right) :
    CallingConditions program (callerMemory disjointLayout bytes)
        [disjointLayout.left, disjointLayout.right] [disjointLayout.output] ∧
    CallingConditions program (callerMemory exactAliasLayout bytes)
        [exactAliasLayout.left, exactAliasLayout.right] [exactAliasLayout.output] ∧
    CallingConditions program (callerMemory partialOverlapLayout bytes)
        [partialOverlapLayout.left, partialOverlapLayout.right] [partialOverlapLayout.output] :=
  ⟨callerMemory_calling program _ caller_layouts_valid.1 bytes sizes identities,
    callerMemory_calling program _ caller_layouts_valid.2.1 bytes sizes identities,
    callerMemory_calling program _ caller_layouts_valid.2.2 bytes sizes identities⟩

theorem disjoint_output_unknown (bytes : Nat → Nat → BitVec 8) (i : Fin 32) :
    ((callerMemory disjointLayout bytes).cells 2 i.val).initialized = false := by
  apply callerMemory_unknown_outside_inputs
  simp [inputByte, disjointLayout]

theorem partial_output_unknown_tail (bytes : Nat → Nat → BitVec 8) :
    ((callerMemory partialOverlapLayout bytes).cells 0 48).initialized = false := by
  apply callerMemory_unknown_outside_inputs
  decide

theorem partial_output_initialized_overlap (bytes : Nat → Nat → BitVec 8) :
    ((callerMemory partialOverlapLayout bytes).cells 0 40).initialized = true := by rfl

#print axioms callerMemory_wellFormed
#print axioms callerMemory_access
#print axioms callerMemory_calling
#print axioms caller_layouts_valid
#print axioms caller_examples_nonvacuous
#print axioms disjoint_output_unknown
#print axioms partial_output_unknown_tail
#print axioms partial_output_initialized_overlap

end UInt256Model.Safety
