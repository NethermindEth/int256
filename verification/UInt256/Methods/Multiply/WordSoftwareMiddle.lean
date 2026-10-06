import UInt256.Methods.Multiply.WordSoftwareLower

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

theorem software_middle (memory : Memory) (frame : Frame) (a b : BitVec 64)
    (output reference lower : Reference) (digits : DigitHomes memory frame a b)
    (lowerSlot : frame.locals[3]? = some (.bytes .word64 lower))
    (lowerRead : read memory lower 8 1 = .ok (numberBytes (softwareLower a b).toNat 8))
    (slot : frame.locals[4]? = some (.bytes .word64 reference))
    (writable : access memory reference 8 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory reference (numberBytes (softwareMiddle a b).toNat 8) 1 = .ok after →
      read after reference 8 1 = .ok (numberBytes (softwareMiddle a b).toNat 8) →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex 53
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
          [.scalar (.i32 (a.setWidth 32))] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex 43
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
        [.scalar (.i32 (a.setWidth 32))] memory = .ok (final, returned) ∧ post final returned := by
  obtain ⟨digit0, slot0, read0⟩ := digits 0
  obtain ⟨digit1, slot1, read1⟩ := digits 1
  obtain ⟨after, stored, written, loaded⟩ := step_store_numeric_local
    (body := wordBody) (pc := 52)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (rest := [.scalar (.i32 (a.setWidth 32))])
    .word64 (.i64 (softwareMiddle a b)) (softwareMiddle a b).toNat rfl slot writable
  have done := continuation after written loaded
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  have load0 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word32 (.i32 ((a >>> 32).setWidth 32))
    ((a >>> 32).setWidth 32).toNat rfl slot0 read0
  have load1 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word32 (.i32 (b.setWidth 32))
    (b.setWidth 32).toNat rfl slot1 read1
  have load3 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word64 (.i64 (softwareLower a b))
    (softwareLower a b).toNat rfl lowerSlot lowerRead
  iterate 9
    apply run_next_exists post found (by rfl)
    first
    | exact load0 _ _
    | exact load1 _ _
    | exact load3 _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simpa only [softwareMiddle, digitLow, digitHigh, BitVec.zeroExtend] using stored
  exact done

#print axioms software_middle
end UInt256Proof.Multiply.Safety
