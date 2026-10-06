import UInt256.Methods.Multiply.WordSafety
import CIL.Safety.UnknownHomes
import CIL.Safety.NumericLocals

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

/-- The software helper may write all six private homes. No initialized read
    is granted by setup: each subsequent read requires its preceding store. -/
theorem word_unknown_homes (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame wordBody args memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity wordBody.localKinds frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed := by
  apply unknown_frame_setup wordBody (by rfl) ?_ (by rfl) memory args wf
  have kinds : wordBody.localKinds = [.word32, .word32, .word32, .word64, .word64, .word64] := by rfl
  simp [kinds]

#print axioms word_unknown_homes
end UInt256Proof.Multiply.Safety

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

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

def inputDigit (a b : BitVec 64) (index : Fin 3) : BitVec 32 :=
  if index = 0 then (a >>> 32).setWidth 32
  else if index = 1 then b.setWidth 32 else (b >>> 32).setWidth 32

def DigitHomes (memory : Memory) (frame : Frame) (a b : BitVec 64) : Prop :=
  ∀ i : Fin 3, ∃ reference, frame.locals[i.val]? = some (.bytes .word32 reference) ∧
    read memory reference 4 1 = .ok (numberBytes (inputDigit a b i).toNat 4)

/-- Initialize all three input-digit homes from the original scalar arguments.
    Writes preserve the caller's bytes and all previously granted access. -/
theorem software_digits (memory : Memory) (boundary : Nat) (frame : Frame)
    (a b : BitVec 64) (output : Reference) (wf : memory.WellFormed)
    (homes : WritableHomes memory boundary wordBody.localKinds frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      DigitHomes after frame a b → after.WellFormed →
      MemoryBelow boundary memory after → AccessBelow memory.nextIdentity memory after →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex 37
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
          [.scalar (.i32 (a.setWidth 32))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex 22
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨r0, s0, bound0, ready0⟩ := homes.home_at 0 .word32 (by rfl)
  obtain ⟨r1, s1, bound1, ready1⟩ := homes.home_at 1 .word32 (by rfl)
  obtain ⟨r2, s2, bound2, ready2⟩ := homes.home_at 2 .word32 (by rfl)
  have distinct01 := Nat.ne_of_lt (homes.ordered 0 1 .word32 .word32 r0 r1 (by decide) s0 s1)
  have distinct02 := Nat.ne_of_lt (homes.ordered 0 2 .word32 .word32 r0 r2 (by decide) s0 s2)
  have distinct12 := Nat.ne_of_lt (homes.ordered 1 2 .word32 .word32 r1 r2 (by decide) s1 s2)
  obtain ⟨allocation1, access1⟩ := access_requirements ready1
  obtain ⟨allocation2, access2⟩ := access_requirements ready2
  apply software_first_store memory frame a b output r0 s0 ready0 post
  intro m0 w0 read0
  apply software_right_store false m0 frame a b output r1 _ s1 (access1.after_write w0).access post
  intro m1 w1 read1
  apply software_right_store true m1 frame a b output r2 _ s2
    ((access2.after_write w0).after_write w1).access post
  intro m2 w2 read2
  have digits : DigitHomes m2 frame a b := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · refine ⟨r0, s0, ?_⟩
      exact write_preserves_disjoint_read w2
        (write_preserves_disjoint_read w1 read0 (Or.inl distinct01)) (Or.inl distinct02)
    · exact ⟨r1, s1, write_preserves_disjoint_read w2 read1 (Or.inl distinct12)⟩
    · exact ⟨r2, s2, read2⟩
  exact continuation m2 digits
    (write_preserves_wellFormed _ _ _ _ _
      (write_preserves_wellFormed _ _ _ _ _ (write_preserves_wellFormed _ _ _ _ _ wf w0) w1) w2)
    (((write_preserves_memory_below _ _ _ _ _ _ bound0 w0).trans
      (write_preserves_memory_below _ _ _ _ _ _ bound1 w1)).trans
      (write_preserves_memory_below _ _ _ _ _ _ bound2 w2))
    (((write_preserves_access_below w0 _).trans (write_preserves_access_below w1 _)).trans
      (write_preserves_access_below w2 _))

#print axioms software_digits
end UInt256Proof.Multiply.Safety
