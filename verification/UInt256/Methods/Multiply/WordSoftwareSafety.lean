import UInt256.Methods.Multiply.WordSoftwareReturn

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

/-- Complete scalar widening multiplication, including unknown local storage,
    checked intermediate reads, caller output and private-frame retirement. -/
theorem software_word_invoke (memory : Memory) (a b : BitVec 64) (output : Reference)
    (wf : memory.WellFormed) (writable : access memory output 8 1 true = .ok ()) :
    ∃ fuel final,
      invoke Extracted.program fuel wordIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] memory =
        .ok (final, [.scalar (.i64 (highProduct a b))]) ∧
      final.WellFormed ∧
      read final output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow memory.nextIdentity memory final ∧
      (∀ id, id < memory.nextIdentity → ∀ offset,
        id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
        final.cells id offset = memory.cells id offset) := by
  let args := [Value.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
  have formed := access_reference_valid _ _ _ _ _ writable
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ formed
  have old := (wf.1 _ _ present).1
  obtain ⟨frame, entered, setup, homes, before, enteredWF⟩ := word_unknown_homes memory args wf
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  let post := fun final returned =>
    returned = [Value.scalar (.i64 (highProduct a b))] ∧ final.WellFormed ∧
    read final output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
    AccessBelow memory.nextIdentity memory final ∧
    (∀ id, id < memory.nextIdentity → ∀ offset,
      id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
      final.cells id offset = memory.cells id offset)
  have body : ∃ fuel final returned,
      run Extracted.program fuel wordIndex 22 args frame [] entered = .ok (final, returned) ∧
      post final returned := by
    apply software_digits entered memory.nextIdentity frame a b output enteredWF homes post
    intro digitMemory digits digitWF digitPreserved digitAuthority
    apply software_products entered digitMemory memory.nextIdentity frame a b output enteredWF
      digitWF homes digitAuthority digits post
    intro productMemory digits products productWF productPreserved productAuthority
    have preserved := (before.trans digitPreserved).trans productPreserved
    have ready : access productMemory output 8 1 true = .ok () :=
      (preserved.access output old 8 1 true).trans writable
    apply software_output productMemory frame a b output products ready post
    intro stored written loaded
    have keepDigit : DigitHomes stored frame a b := by
      intro i
      obtain ⟨r, slot, readback⟩ := digits i
      have bound := homes.home_bound i.val .word32 r slot
      exact ⟨r, slot, write_preserves_disjoint_read written readback (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le old bound)))⟩
    have keepProduct : ProductHomes stored frame a b := by
      intro i
      obtain ⟨r, slot, readback⟩ := products i
      have bound := homes.home_bound (3 + i.val) .word64 r slot
      exact ⟨r, slot, write_preserves_disjoint_read written readback (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le old bound)))⟩
    have retired := leaveFrame_preserves_memory_below frame stored memory.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨14, leaveFrame frame stored, [.scalar (.i64 (highProduct a b))],
      software_return stored frame a b output keepDigit keepProduct, rfl,
      leaveFrame_preserves_wellFormed _ _ (write_preserves_wellFormed _ _ _ _ _ productWF written),
      (retired.read output old 8 1).trans loaded,
      preserved.accessBelow.trans ((write_preserves_access_below written _).trans retired.accessBelow), ?_⟩
    intro id bound offset outside
    rw [retired.cells id bound offset]
    exact (write_outside _ _ _ _ _ id offset written (by simpa only [numberBytes, List.length_map, List.length_range] using outside)).trans
      (preserved.cells id bound offset)
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  have profile : wordBody.profile = Extracted.profile := by rfl
  have start : ∃ fuel final returned,
      run Extracted.program fuel wordIndex 0 args frame [] entered = .ok (final, returned) ∧
      post final returned := by
    iterate 4
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, profile, Extracted.profile, CIL.FeatureProfile.evaluate,
          checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact body
  obtain ⟨fuel, final, returned, ran, same, guarantees⟩ := start
  subst returned
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, guarantees⟩
  change invoke Extracted.program fuel wordIndex args memory = _
  simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

#print axioms software_word_invoke
end UInt256Proof.Multiply.Safety
