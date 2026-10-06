import UInt256.Methods.Multiply.WordSoftwareDigits
import UInt256.Methods.Multiply.WordProduct

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

/-- The first partial product reads an initialized digit and initializes its
    own 64-bit home. The low left digit remains on the evaluation stack. -/
theorem software_lower (memory : Memory) (frame : Frame) (a b : BitVec 64)
    (output reference : Reference) (digits : DigitHomes memory frame a b)
    (slot : frame.locals[3]? = some (.bytes .word64 reference))
    (writable : access memory reference 8 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory reference (numberBytes (softwareLower a b).toNat 8) 1 = .ok after →
      read after reference 8 1 = .ok (numberBytes (softwareLower a b).toNat 8) →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex 43
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
          [.scalar (.i32 (a.setWidth 32))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex 37
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
        [.scalar (.i32 (a.setWidth 32))] memory = .ok (final, returned) ∧ post final returned := by
  obtain ⟨digit, digitSlot, digitRead⟩ := digits 1
  obtain ⟨after, stored, written, loaded⟩ := step_store_numeric_local
    (body := wordBody) (pc := 42)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (rest := [.scalar (.i32 (a.setWidth 32))])
    .word64 (.i64 (softwareLower a b)) (softwareLower a b).toNat rfl slot writable
  have done := continuation after written loaded
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word32 (.i32 (b.setWidth 32))
    (b.setWidth 32).toNat rfl digitSlot digitRead
  iterate 5
    apply run_next_exists post found (by rfl)
    first
    | exact load _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simpa only [softwareLower, digitLow, BitVec.zeroExtend] using stored
  exact done

#print axioms software_lower
end UInt256Proof.Multiply.Safety
