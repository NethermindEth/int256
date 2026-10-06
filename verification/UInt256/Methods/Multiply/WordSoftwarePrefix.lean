import UInt256.Methods.Multiply.WordSoftwareSetup
import CIL.Safety.NumericLocals

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

/-- The software path initializes its first unknown home from the high digit
    of the initial left word, retaining the low digit on the evaluation stack. -/
theorem software_first_store (memory : Memory) (frame : Frame) (a b : BitVec 64)
    (output reference : Reference)
    (slot : frame.locals[0]? = some (.bytes .word32 reference))
    (writable : access memory reference 4 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory reference (numberBytes ((a >>> 32).setWidth 32).toNat 4) 1 = .ok after →
      read after reference 4 1 = .ok (numberBytes ((a >>> 32).setWidth 32).toNat 4) →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex 29
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
          [.scalar (.i32 (a.setWidth 32))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex 22
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨after, stored, written, loaded⟩ := step_store_numeric_local
    (body := wordBody) (pc := 28)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (rest := [.scalar (.i32 (a.setWidth 32))])
    .word32 (.i32 ((a >>> 32).setWidth 32)) ((a >>> 32).setWidth 32).toNat rfl slot writable
  have done := continuation after written loaded
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  iterate 6
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) stored
  exact done

#print axioms software_first_store

/-- Initialize either right-hand digit without reading any private local. -/
theorem software_right_store (high : Bool) (memory : Memory) (frame : Frame)
    (a b : BitVec 64) (output reference : Reference) (stack : List Value)
    (slot : frame.locals[if high then 2 else 1]? = some (.bytes .word32 reference))
    (writable : access memory reference 4 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory reference (numberBytes ((if high then b >>> 32 else b).setWidth 32).toNat 4) 1 = .ok after →
      read after reference 4 1 = .ok (numberBytes ((if high then b >>> 32 else b).setWidth 32).toNat 4) →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex (if high then 37 else 32)
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame stack after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex (if high then 32 else 29)
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame stack memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨after, stored, written, loaded⟩ := step_store_numeric_local
    (body := wordBody) (pc := if high then 36 else 31)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]) (rest := stack)
    .word32 (.i32 ((if high then b >>> 32 else b).setWidth 32))
    ((if high then b >>> 32 else b).setWidth 32).toNat rfl slot writable
  have done := continuation after written loaded
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  cases high
  · iterate 2
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored done
  · iterate 4
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored done

#print axioms software_right_store
end UInt256Proof.Multiply.Safety
