import CIL.Safety.AccessRequirements
import CIL.Safety.StaticReferences

namespace CIL.Safety

theorem access_requirements {m : Memory} {r : Reference} {width alignment : Nat}
    {writing : Bool} (h : access m r width alignment writing = .ok ()) :
    ∃ allocation, AccessRequirements m r width alignment writing allocation := by
  have formed := access_reference_valid _ _ _ _ _ h
  obtain ⟨allocation, present, live, position⟩ := formed_reference_live _ _ _ formed
  have lookup : liveAllocation m r.allocation = .ok allocation := by
    simp [liveAllocation, present, live, Pure.pure, Except.pure]
  unfold access at h
  simp only [formed, lookup, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i slots
    simp only [Pure.pure, Except.pure] at h
    split at h
    · rename_i extent
      split at h
      · rename_i aligned
        split at h
        · simp at h
        · rename_i mutable
          split at h
          · rename_i permission
            refine ⟨allocation, present, live, position, ?_, extent, ?_, ?_, ?_⟩
            · intro slot member overlap
              apply slots
              exact List.any_eq_true.mpr ⟨slot, member, by simp [overlap]⟩
            · simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using aligned
            · intro writes immutable
              simp [writes, immutable] at mutable
            · intro i bound
              exact List.all_eq_true.mp permission i (List.mem_range.mpr bound)
          · cases h
      · simp at h
    · simp at h

/-- A nonempty subinterval of an admitted access is itself accessible with
    byte alignment. Formation, GC layout and API authority are retained. -/
theorem AccessRequirements.slice {m : Memory} {r : Reference} {width alignment : Nat}
    {writing : Bool} {allocation : Allocation}
    (ready : AccessRequirements m r width alignment writing allocation) (wellFormed : m.WellFormed)
    (start count : Nat) (nonempty : 0 < count) (within : start + count ≤ width) :
    AccessRequirements m { r with offset := r.offset + start } count 1 writing allocation := by
  have interior : r.offset + start < allocation.layout.size := by have := ready.extent; omega
  have native := (wellFormed.1 _ _ ready.present).2.1
  refine ⟨ready.present, ready.live, ?_, ?_, ?_, ?_, ready.mutable, ?_⟩
  · simp [validPosition, interior, show r.offset + start < nativeLimit by omega]
  · intro slot member overlap
    dsimp only at overlap
    apply ready.layout slot member
    constructor <;> omega
  · change r.offset + start + count ≤ allocation.layout.size
    have := ready.extent
    omega
  · simp [Nat.mod_one]
  · intro i bound
    have permission := ready.permission (start + i) (by omega)
    simpa only [Nat.add_assoc] using permission

theorem read_slice {m : Memory} {r : Reference} {width alignment : Nat} {bytes : List (BitVec 8)}
    (wellFormed : m.WellFormed) (h : read m r width alignment = .ok bytes)
    (start count : Nat) (nonempty : 0 < count) (within : start + count ≤ width) :
    read m { r with offset := r.offset + start } count 1 =
      .ok ((List.range count).map fun i => (m.cells r.allocation (r.offset + start + i)).bits) := by
  have accessOK : access m r width alignment false = .ok () := by
    unfold read at h
    cases ha : access m r width alignment false with
    | error fault => simp [ha, Bind.bind, Except.bind] at h
    | ok value => cases value; rfl
  obtain ⟨allocation, ready⟩ := access_requirements accessOK
  apply read_snapshot (ready.slice wellFormed start count nonempty within)
  intro i bound
  have initialized := read_requires_initialization _ _ _ _ _ h (start + i) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_assoc] using initialized

theorem AccessRequirements.add_slice {m : Memory} {r : Reference} {width alignment : Nat}
    {writing : Bool} {allocation : Allocation}
    (ready : AccessRequirements m r width alignment writing allocation) (wellFormed : m.WellFormed)
    (size index count : Nat) (nonempty : 0 < count) (within : size * index + count ≤ width) :
    add m r size (BitVec.ofNat 64 index) = .ok { r with offset := r.offset + size * index } := by
  have source := access_reference_valid _ _ _ _ _ ready.access
  have target := access_reference_valid _ _ _ _ _
    (ready.slice wellFormed (size * index) count nonempty within).access
  have bound : r.offset + size * index < 2^64 := by
    have extent := ready.extent
    have native := (wellFormed.1 _ _ ready.present).2.1
    change allocation.layout.size < 2^64 at native
    omega
  simp only [add, source, Bind.bind, Except.bind, BitVec.ofNat_mul_ofNat,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  exact target

/-- A checked subread returns exactly the corresponding bytes from the admitted
    snapshot, not merely some initialized bytes in the same allocation. -/
theorem read_slice_bytes {m : Memory} {r : Reference} {width alignment : Nat}
    {bytes : List (BitVec 8)} (wellFormed : m.WellFormed)
    (loaded : read m r width alignment = .ok bytes)
    (start count : Nat) (nonempty : 0 < count) (within : start + count ≤ width) :
    read m { r with offset := r.offset + start } count 1 =
      .ok ((bytes.drop start).take count) := by
  rw [read_slice wellFormed loaded start count nonempty within]
  congr 1
  rw [read_result_snapshot loaded]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro i hi hj
    simp [Nat.add_assoc]

#print axioms read_slice_bytes
#print axioms access_requirements
#print axioms AccessRequirements.slice
#print axioms read_slice
#print axioms AccessRequirements.add_slice

end CIL.Safety
