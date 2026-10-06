import CIL.Safety.RelocationAddress
import CIL.Safety.Calling

namespace CIL.Safety.Tests

deriving instance DecidableEq for Except

def wordAllocation : Allocation :=
  { kind := .managedHeap, layout := { size := 40, alignment := 8 }, sentinels := [40] }

def initial : Memory :=
  { allocations := fun id => if id = 0 then some wordAllocation else none
    cells := fun _ offset => { bits := if offset = 8 then 1 else 0, initialized := offset < 32 }
    views := [{ allocation := 0, start := 0, length := 32, readable := true, writable := false },
      { allocation := 0, start := 8, length := 32, readable := false, writable := true }]
    nextIdentity := 1 }

def source : Reference := ⟨0, 0⟩
def target : Reference := ⟨0, 8⟩

theorem initial_wellFormed : initial.WellFormed := by
  constructor
  · intro id a ha
    simp only [initial] at ha
    split at ha
    · simp only [Option.some.injEq] at ha
      subst a
      subst id
      constructor
      · decide
      · simp [Allocation.WellFormed, wordAllocation, nativeLimit]
    · cases ha
  · intro view hv
    simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> exact ⟨wordAllocation, rfl, by decide⟩

theorem overlapping_valid_initial_call : ValidCall initial [⟨source, 32⟩] [⟨target, 32⟩] := by
  refine ⟨initial_wellFormed, ?_, ?_⟩
  · intro input hi
    simp only [List.mem_singleton] at hi
    subst input
    exact ⟨_, rfl⟩
  · intro output ho
    simp only [List.mem_singleton] at ho
    subst output
    rfl

theorem interior_formation : form initial target = .ok target := by decide

theorem specified_end_formation : form initial ⟨0, 40⟩ = .ok ⟨0, 40⟩ := by decide

theorem end_not_dereferenceable : read initial ⟨0, 40⟩ 1 1 = .error .outsideAllocation := by decide

theorem null_formation : validManagedReference initial .null = true := by rfl

theorem null_access_rejected : dereference initial .null 8 1 = .error .nullDereference := by rfl

theorem invalid_intermediate : add initial source 8 (BitVec.ofInt 64 (-1)) = .error .invalidReference := by decide

theorem unused_overread : read initial source 48 1 = .error .outsideAllocation := by decide

theorem outside_api_view : read initial ⟨0, 32⟩ 8 1 = .error .unreadable := by decide

theorem partial_initialization :
    read { initial with views := [⟨0, 0, 40, true, true⟩] }
      target 32 1 = .error .uninitialized := by rfl

theorem restore_after_forbidden_write : write initial source [0] 1 = .error .unwritable := by rfl

theorem full_output_initialization :
    match copy initial source target 32 with
    | .error _ => False
    | .ok final => ∀ i : Fin 32, (final.cells 0 (8 + i.val)).initialized = true := by
  change ∀ i : Fin 32, _
  decide

theorem overlapping_snapshot :
    match copy initial source target 32 with
    | .error _ => False
    | .ok final => final.cells 0 8 = ⟨0, true⟩ ∧ final.cells 0 16 = ⟨1, true⟩ ∧
        final.cells 0 24 = ⟨0, true⟩ ∧ final.cells 0 32 = ⟨0, true⟩ := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def writeOnly : Memory := { initial with views := [⟨0, 0, 40, false, true⟩] }

theorem write_only_output_initially_unreadable :
    read writeOnly ⟨0, 32⟩ 1 1 = .error .unreadable := by rfl

theorem initialized_output_readable :
    match write writeOnly ⟨0, 32⟩ [42] 1 with
    | .error _ => False
    | .ok final => read final ⟨0, 32⟩ 1 1 = .ok [42] := by rfl

theorem write_does_not_expose_neighbor :
    match write writeOnly ⟨0, 32⟩ [42] 1 with
    | .error _ => False
    | .ok final => read final ⟨0, 33⟩ 1 1 = .error .unreadable ∧
        (final.cells 0 33).initialized = false := by exact ⟨rfl, rfl⟩

theorem overlapping_output_readable_after_copy :
    match copy initial source target 32 with
    | .error _ => False
    | .ok final => read final target 32 1 = read initial source 32 1 := by rfl

theorem unaligned_access_allowed : read initial ⟨0, 1⟩ 16 1 =
    .ok ((List.range 16).map fun i => if i = 7 then 1 else 0) := by decide

theorem aligned_access_rejected : read initial ⟨0, 1⟩ 16 16 = .error .alignment := by decide

#print axioms unaligned_access_allowed
#print axioms aligned_access_rejected

theorem cannot_change_allocation :
    let adjacent := { initial with allocations := (fun id =>
      if id = 1 then some wordAllocation else initial.allocations id) }
    add adjacent ⟨0, 32⟩ 8 2 = .error .invalidReference := by rfl

theorem stale_reference_rejected :
    form (expire initial 0) target = .error .expiredLifetime := by decide

theorem recycled_slot_distinct_identity :
    match allocate (expire initial 0) { wordAllocation with kind := .frame 1 } with
    | .error _ => False
    | .ok (id, final) => id = 1 ∧ form final target = .error .expiredLifetime ∧
        (final.cells id 0).initialized = false := by
  exact ⟨rfl, rfl, rfl⟩

theorem native_scaling_wrap : add initial source (2^63) 2 = .ok source := by decide

theorem larger_native_offset_invalid :
    add initial source 8 2305843009213693951 = .error .invalidReference := by decide

def containingGcField : Memory :=
  { initial with allocations := (fun id => if id = 0 then
      some { wordAllocation with layout := { size := 48, alignment := 8, referenceSlots := [(40, 8)] } }
    else none) }

theorem unrelated_gc_field_allowed : read containingGcField source 32 1 =
    read initial source 32 1 := by rfl

theorem gc_field_access_rejected : read containingGcField ⟨0, 40⟩ 8 1 = .error .unsupportedLayout := by rfl

theorem different_placements :
    concreteAddress (fun _ => 64) target ≠ concreteAddress (fun _ => 128) target := by
  change (72 : BitVec 64) ≠ 136
  bv_decide

theorem placement_does_not_change_validity :
    (relocate ⟨initial, fun _ => 4096⟩ (fun _ => 8192)).form target = .ok target := by rfl

#print axioms full_output_initialization
#print axioms overlapping_snapshot
#print axioms invalid_intermediate
#print axioms recycled_slot_distinct_identity
#print axioms CIL.Safety.add_preserves_provenance
#print axioms CIL.Safety.formed_reference_live
#print axioms CIL.Safety.access_within_allocation
#print axioms CIL.Safety.access_requires_permission
#print axioms CIL.Safety.expired_reference
#print axioms CIL.Safety.write_initializes
#print axioms CIL.Safety.read_requires_initialization
#print axioms CIL.Safety.relocation_preserves_reference_validity
#print axioms CIL.Safety.relocation_preserves_read
#print axioms CIL.Safety.guaranteed_alignment_at_placement
#print axioms overlapping_valid_initial_call
#print axioms initialized_output_readable
#print axioms write_does_not_expose_neighbor
#print axioms overlapping_output_readable_after_copy
#print axioms CIL.Safety.write_preserves_write_permission
#print axioms CIL.Safety.write_read_permission
#print axioms CIL.Safety.write_preserves_wellFormed
#print axioms CIL.Safety.expire_preserves_wellFormed
#print axioms CIL.Safety.allocate_preserves_wellFormed


/-- Legal relocation can remove accidental 16-byte alignment while retaining
all alignment promised by this allocation (eight bytes). -/
theorem relocation_changes_incidental_alignment :
    LegalRelocation initial (fun _ => 128) (fun _ => 136) ∧
      (concreteAddress (fun _ => 128) source).toNat % 16 = 0 ∧
      (concreteAddress (fun _ => 136) source).toNat % 16 = 8 := by
  simp [LegalRelocation, Placement.Valid, initial, wordAllocation, nativeLimit,
    concreteAddress, source]
  constructor <;> intro left right a b different hl ha hr
  all_goals exact False.elim (different (hl.trans hr.symm))

/-- A coincidentally aligned current placement cannot authorize an instruction
whose alignment requirement exceeds the allocation guarantee. -/
theorem incidental_alignment_rejected :
    access initial source 16 16 false = .error .alignment := by decide

#print axioms relocation_changes_incidental_alignment
#print axioms incidental_alignment_rejected
end CIL.Safety.Tests
