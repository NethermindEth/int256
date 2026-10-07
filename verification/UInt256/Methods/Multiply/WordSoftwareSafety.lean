import UInt256.Methods.Multiply.WordSoftwareProducts

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

theorem software_output (memory : Memory) (frame : Frame) (a b : BitVec 64)
    (output : Reference) (products : ProductHomes memory frame a b)
    (writable : access memory output 8 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory output (numberBytes (lowProduct a b).toNat 8) 1 = .ok after →
      read after output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex 71
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex 62
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨r3, s3, read3⟩ := products 0
  obtain ⟨r5, s5, read5⟩ := products 2
  have length : (numberBytes (lowProduct a b).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨after, written⟩ := write_succeeds
    (bytes := numberBytes (lowProduct a b).toNat 8) (by simpa only [length] using writable)
  have loaded := write_readback _ _ _ _ _ written
  rw [length] at loaded
  have done := continuation after written loaded
  have formed := access_reference_valid _ _ _ _ _ writable
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  have load3 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word64 (.i64 (softwareLower a b))
    (softwareLower a b).toNat rfl s3 read3
  have load5 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word64 (.i64 (softwareUpper a b))
    (softwareUpper a b).toNat rfl s5 read5
  have stored : step wordBody .store64 70
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
      [.scalar (.i64 (softwareLow a b)), .reference (.address output)] memory =
      .ok (.next 71 [] frame after) := by
    simp only [step, pureArity, instruction, storeValue, referenceAt, checkedValue, numericValue, formValue, formed,
      softwareLow_correct, checkedAt, Except.mapError, written,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  iterate 8
    apply run_next_exists post found (by rfl)
    first
    | exact load3 _ _
    | exact load5 _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          referenceAt, formValue, formed, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simpa only [softwareLow, digitLow, BitVec.zeroExtend] using stored
  exact done

#print axioms software_output
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

/-- Return the mathematical high word from the initialized input digits and
    partial products, retiring the actual helper frame normally. -/
theorem software_return (memory : Memory) (frame : Frame) (a b : BitVec 64)
    (output : Reference) (digits : DigitHomes memory frame a b)
    (products : ProductHomes memory frame a b) :
    run Extracted.program 14 wordIndex 71
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i64 (highProduct a b))]) := by
  obtain ⟨r0, s0, read0⟩ := digits 0
  obtain ⟨r2, s2, read2⟩ := digits 2
  obtain ⟨r4, s4, read4⟩ := products 1
  obtain ⟨r5, s5, read5⟩ := products 2
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  have load0 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word32 (.i32 ((a >>> 32).setWidth 32))
    ((a >>> 32).setWidth 32).toNat rfl s0 read0
  have load2 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word32 (.i32 ((b >>> 32).setWidth 32))
    ((b >>> 32).setWidth 32).toNat rfl s2 read2
  have load4 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word64 (.i64 (softwareMiddle a b))
    (softwareMiddle a b).toNat rfl s4 read4
  have load5 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word64 (.i64 (softwareUpper a b))
    (softwareUpper a b).toNat rfl s5 read5
  iterate 13
    apply Eq.trans
    · apply run_next (body := wordBody) found (by rfl)
      first
      | exact load0 _ _
      | exact load2 _ _
      | exact load4 _ _
      | exact load5 _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  change run Extracted.program 1 wordIndex 84
    [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
    [.scalar (.i64 (softwareHigh a b))] memory = _
  rw [softwareHigh_correct, run]
  have fetched : wordBody.code[84]? = some .ret := by rfl
  simp only [found, fetched]
  rfl

#print axioms software_return
end UInt256Proof.Multiply.Safety

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
  exact invoke_of_run found checked setup ran

#print axioms software_word_invoke
end UInt256Proof.Multiply.Safety
