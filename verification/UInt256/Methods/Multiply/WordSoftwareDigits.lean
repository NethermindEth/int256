import UInt256.Methods.Multiply.WordSoftwarePrefix

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
