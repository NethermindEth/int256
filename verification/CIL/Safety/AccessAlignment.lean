import CIL.Safety.AccessSlices
import CIL.Safety.Relocation

namespace CIL.Safety

/-- A successful access establishes the requested alignment at every legal
    placement, even when it is weaker than the allocation's alignment. This
    uses guaranteed layout alignment, never incidental physical placement. -/
theorem access_alignment_at_placement {m : Memory} {r : Reference}
    {width alignment : Nat} {writing : Bool} (p : Placement) (placed : p.Valid m)
    (checked : access m r width alignment writing = .ok ()) :
    0 < alignment ∧ (p r.allocation + r.offset) % alignment = 0 := by
  obtain ⟨allocation, ready⟩ := access_requirements checked
  have base := (placed.1 r.allocation allocation ready.present ready.live).2.2
  have divides : alignment ∣ p r.allocation :=
    Nat.dvd_trans (Nat.dvd_of_mod_eq_zero ready.aligned.2.1)
      (Nat.dvd_of_mod_eq_zero base)
  exact ⟨ready.aligned.1, Nat.mod_eq_zero_of_dvd
    (Nat.dvd_add divides (Nat.dvd_of_mod_eq_zero ready.aligned.2.2))⟩

/-- Successful value loading cannot bypass the full checked read, regardless
    of the width's later scalar/vector interpretation. -/
theorem loadValue_checked_read {m : Memory} {reference : ManagedReference}
    {width : Nat} {value : CIL.Value}
    (loaded : loadValue m reference width = .ok value) :
    ∃ r bytes, reference = .address r ∧ read m r width 1 = .ok bytes := by
  cases reference with
  | null => simp [loadValue, dereference, checkedAt, Except.mapError,
      Bind.bind, Except.bind] at loaded
  | address r =>
    cases hread : read m r width 1 with
    | error fault => simp [loadValue, dereference, hread, checkedAt,
        Except.mapError, Bind.bind, Except.bind] at loaded
    | ok bytes => exact ⟨r, bytes, rfl, hread⟩

/-- Byte alignment at the supported ordinary value-load boundary imposes no
    hidden natural/vector alignment on a caller offset. Other read obligations
    still come from the actual checked access. This is a model theorem, not a
    theorem about CLR lowering; see ALIGNMENT.md for that correspondence audit. -/
theorem loadValue_access_requirements {m : Memory} {reference : ManagedReference}
    {width : Nat} {value : CIL.Value}
    (loaded : loadValue m reference width = .ok value) :
    ∃ r allocation, reference = .address r ∧
      AccessRequirements m r width 1 false allocation := by
  obtain ⟨r, bytes, href, hread⟩ := loadValue_checked_read loaded
  have checked : access m r width 1 false = .ok () := by
    unfold read at hread
    cases haccess : access m r width 1 false with
    | error fault => simp [haccess, Bind.bind, Except.bind] at hread
    | ok result => cases result; rfl
  obtain ⟨allocation, ready⟩ := access_requirements checked
  exact ⟨r, allocation, href, ready⟩

private theorem checkedAt_success {reference : ManagedReference} {width : Nat}
    {result : Checked α} {value : α} (checked : checkedAt reference width result = .ok value) :
    result = .ok value := by
  cases result <;> simp_all [checkedAt, Except.mapError]

/-- Every supported scalar/vector store uses an actual checked byte write. -/
theorem storeValue_checked_write {m final : Memory} {reference : ManagedReference}
    {value : CIL.Value} (stored : storeValue m reference value = .ok final) :
    ∃ r bytes, reference = .address r ∧ write m r bytes 1 = .ok final := by
  cases value <;> cases reference <;>
    simp only [storeValue, referenceAt, Bind.bind, Except.bind] at stored <;>
    try cases stored
  all_goals exact ⟨_, _, rfl, checkedAt_success stored⟩

theorem storeValue_access_requirements {m final : Memory} {reference : ManagedReference}
    {value : CIL.Value} (stored : storeValue m reference value = .ok final) :
    ∃ r bytes allocation, reference = .address r ∧ write m r bytes 1 = .ok final ∧
      AccessRequirements m r bytes.length 1 true allocation := by
  obtain ⟨r, bytes, href, hwritten⟩ := storeValue_checked_write stored
  have checked : access m r bytes.length 1 true = .ok () := by
    unfold write at hwritten
    cases haccess : access m r bytes.length 1 true with
    | error fault => simp [haccess, Bind.bind, Except.bind] at hwritten
    | ok result => cases result; rfl
  obtain ⟨allocation, ready⟩ := access_requirements checked
  exact ⟨r, bytes, allocation, href, hwritten, ready⟩

#print axioms access_alignment_at_placement
#print axioms loadValue_checked_read
#print axioms loadValue_access_requirements
#print axioms storeValue_checked_write
#print axioms storeValue_access_requirements

end CIL.Safety
