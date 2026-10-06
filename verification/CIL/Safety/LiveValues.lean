import CIL.Safety.ExecutionLifetime

namespace CIL.Safety

/-- Reference validity is independent of readable initialization and access
    width. A span's accessible bytes are checked by the memory operation. -/
def Value.Valid (m : Memory) : Value → Prop
  | .scalar value => numericValue value = true
  | .reference .null | .span .null _ => True
  | .reference (.address r) | .span (.address r) _ => form m r = .ok r

def ValuesValid (m : Memory) (values : List Value) : Prop :=
  ∀ value ∈ values, value.Valid m

theorem ValuesValid.append {m : Memory} {left right : List Value}
    (hl : ValuesValid m left) (hr : ValuesValid m right) : ValuesValid m (left ++ right) := by
  intro value member
  rcases List.mem_append.mp member with member | member
  · exact hl _ member
  · exact hr _ member

theorem ValuesValid.head {m : Memory} {value : Value} {values : List Value}
    (valid : ValuesValid m (value :: values)) : value.Valid m := valid _ (by simp)

theorem ValuesValid.tail {m : Memory} {value : Value} {values : List Value}
    (valid : ValuesValid m (value :: values)) : ValuesValid m values :=
  fun _ member => valid _ (List.mem_cons_of_mem _ member)

theorem ValuesValid.cons {m : Memory} {value : Value} {values : List Value}
    (head : value.Valid m) (tail : ValuesValid m values) : ValuesValid m (value :: values) := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail _ member

theorem form_returns_input (m : Memory) (r result : Reference) (h : form m r = .ok result) :
    result = r := by
  unfold form at h
  cases hl : liveAllocation m r.allocation <;>
    simp only [hl, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · cases h
  · split at h
    · exact Except.ok.inj h |>.symm
    · cases h

theorem formValue_returns_input (m : Memory) (r : ManagedReference) (value : Value)
    (h : formValue m r = .ok value) : value = .reference r := by
  cases r with
  | null => cases h; rfl
  | address r =>
    simp only [formValue] at h
    cases hf : form m r <;>
      simp only [hf, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    · cases h
    · rename_i formed
      have same := form_returns_input _ _ _ hf
      cases h
      rw [same]

theorem formValue_result_valid (m : Memory) (r : ManagedReference) (value : Value)
    (h : formValue m r = .ok value) : value.Valid m := by
  have same := formValue_returns_input _ _ _ h
  subst value
  cases r with
  | null => exact True.intro
  | address r =>
    cases hf : form m r <;>
      simp only [formValue, hf, checkedAt, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at h
    · cases h
    · rename_i formed
      have same := form_returns_input _ _ _ hf
      subst formed
      exact hf

theorem checkedValue_valid (m : Memory) (value result : Value)
    (h : checkedValue m value = .ok result) : result = value ∧ result.Valid m := by
  cases value with
  | scalar value =>
    simp only [checkedValue] at h
    split at h
    · rename_i numeric
      cases h
      exact ⟨rfl, numeric⟩
    · cases h
  | reference r =>
    exact ⟨formValue_returns_input _ _ _ h, formValue_result_valid _ _ _ h⟩
  | span r length =>
    simp only [checkedValue] at h
    cases hf : formValue m r <;> simp only [hf, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    · cases h
    · have valid := formValue_result_valid _ _ _ hf
      have same := formValue_returns_input _ _ _ hf
      cases h
      rw [same] at valid
      cases r <;> exact ⟨rfl, valid⟩

theorem checkedValue_of_valid (m : Memory) (value : Value) (valid : value.Valid m) :
    checkedValue m value = .ok value := by
  cases value with
  | scalar value => simp only [Value.Valid] at valid; simp [checkedValue, valid]
  | reference r => cases r <;>
      simp_all [Value.Valid, checkedValue, formValue, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  | span r length => cases r <;>
      simp_all [Value.Valid, checkedValue, formValue, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem ValuesValid.preserve {m result : Memory} {values : List Value}
    (valid : ValuesValid m values) (hm : m.WellFormed) (ext : AllocationExtension m result) :
    ValuesValid result values := by
  intro value member
  have hv := valid value member
  cases value with
  | scalar value => exact hv
  | reference r =>
    cases r with
    | null => exact True.intro
    | address r => exact ext.preserves_reference hm r r hv
  | span r length =>
    cases r with
    | null => exact True.intro
    | address r => exact ext.preserves_reference hm r r hv

theorem checkedValues_valid (m : Memory) (values result : List Value)
    (h : values.mapM (checkedValue m) = .ok result) : result = values ∧ ValuesValid m result := by
  induction values generalizing result with
  | nil => cases h; exact ⟨rfl, by simp [ValuesValid]⟩
  | cons value values ih =>
    simp only [List.mapM_cons] at h
    cases hc : checkedValue m value <;> simp only [hc, Bind.bind, Except.bind] at h
    · cases h
    · rename_i checked
      have first := checkedValue_valid _ _ _ hc
      cases hr : values.mapM (checkedValue m) <;> simp only [hr, Pure.pure, Except.pure] at h
      · cases h
      · rename_i rest
        have tail := ih rest hr
        cases h
        refine ⟨by rw [first.1, tail.1], ?_⟩
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact first.2
        · exact tail.2 _ member

#print axioms checkedValue_valid
#print axioms checkedValue_of_valid
#print axioms ValuesValid.preserve
#print axioms checkedValues_valid

end CIL.Safety
