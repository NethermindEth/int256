import CIL.Safety.Relocation

namespace CIL.Safety

/-- A legal placement gives a non-null, non-wrapping address even for an
explicitly admitted end sentinel. It does not grant permission to dereference. -/
theorem concreteAddress_bounds (p : Placement) (m : Memory) (hp : p.Valid m)
    (r : Reference) (a : Allocation) (ha : m.allocations r.allocation = some a)
    (hlive : a.live = true) (hoffset : r.offset ≤ a.layout.size) :
    0 < (concreteAddress p r).toNat ∧
      (concreteAddress p r).toNat = p r.allocation + r.offset := by
  have bounds := hp.1 r.allocation a ha hlive
  have limit : p r.allocation + r.offset < 2^64 := by
    change p r.allocation + r.offset < nativeLimit
    omega
  have address : (concreteAddress p r).toNat = p r.allocation + r.offset := by
    change (p r.allocation + r.offset) % 2^64 = p r.allocation + r.offset
    exact Nat.mod_eq_of_lt limit
  constructor
  · rw [address]
    omega
  · exact address

/-- Live interior addresses cannot collide across distinct allocations.
End sentinels are deliberately excluded: one allocation's end can share the
numerical address of its neighbour's beginning without sharing provenance. -/
theorem concreteAddress_injective (p : Placement) (m : Memory) (hp : p.Valid m)
    (left right : Reference) (a b : Allocation)
    (ha : m.allocations left.allocation = some a)
    (hb : m.allocations right.allocation = some b)
    (hla : a.live = true) (hlb : b.live = true)
    (hoa : left.offset < a.layout.size) (hob : right.offset < b.layout.size)
    (same : concreteAddress p left = concreteAddress p right) : left = right := by
  have la := concreteAddress_bounds p m hp left a ha hla (Nat.le_of_lt hoa)
  have rb := concreteAddress_bounds p m hp right b hb hlb (Nat.le_of_lt hob)
  have numbers := congrArg BitVec.toNat same
  rw [la.2, rb.2] at numbers
  have ids : left.allocation = right.allocation := by
    by_cases ids : left.allocation = right.allocation
    · exact ids
    · have separated := hp.2 left.allocation right.allocation a b ids ha hb hla hlb
      omega
  have offsets : left.offset = right.offset := by
    rw [ids] at numbers
    omega
  cases left
  cases right
  simp_all

#print axioms concreteAddress_bounds
#print axioms concreteAddress_injective
/-- An accepted access uses runtime-guaranteed alignment, rather than a
stronger alignment that happens to hold before relocation. -/
theorem access_guaranteed_alignment (m : Memory) (r : Reference)
    (width alignment : Nat) (writing : Bool)
    (checked : access m r width alignment writing = .ok ()) :
    ∃ a, m.allocations r.allocation = some a ∧ a.live = true ∧
      0 < alignment ∧ a.layout.alignment % alignment = 0 ∧ r.offset % alignment = 0 := by
  unfold access at checked
  cases hf : form m r <;> simp only [hf, Bind.bind, Except.bind] at checked
  · cases checked
  · cases ha : liveAllocation m r.allocation <;> simp only [ha] at checked
    · cases checked
    · split at checked
      · simp at checked
      · simp only [Pure.pure, Except.pure] at checked
        split at checked
        · split at checked
          · rename_i alignment_ok
            refine ⟨_, (liveAllocation_ok _ _ _ ha).1, (liveAllocation_ok _ _ _ ha).2, ?_⟩
            simpa [Bool.and_eq_true, and_assoc] using alignment_ok
          · simp at checked
        · simp at checked

/-- Every physical placement allowed by the allocation contract respects the
alignment of every checked access; no fixed-address assumption is needed. -/
theorem checked_access_aligned_at_placement (p : Placement) (m : Memory)
    (hp : p.Valid m) (r : Reference) (width alignment : Nat) (writing : Bool)
    (checked : access m r width alignment writing = .ok ()) :
    (concreteAddress p r).toNat % alignment = 0 := by
  obtain ⟨a, ha, hlive, _, hsize⟩ := access_guaranteed_alignment m r width alignment writing checked
  obtain ⟨b, hb, _, bounds⟩ := access_within_allocation m r width alignment writing checked
  have same : b = a := Option.some.inj (hb.symm.trans ha)
  subst b
  have address := concreteAddress_bounds p m hp r a ha hlive (by omega)
  rw [address.2]
  have base := (hp.1 r.allocation a ha hlive).2.2
  have divided := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hsize.1) (Nat.dvd_of_mod_eq_zero base)
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd divided, hsize.2]

#print axioms access_guaranteed_alignment
#print axioms checked_access_aligned_at_placement
end CIL.Safety
