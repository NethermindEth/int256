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
