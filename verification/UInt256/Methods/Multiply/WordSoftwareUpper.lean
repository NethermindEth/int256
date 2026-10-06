import UInt256.Methods.Multiply.WordSoftwareMiddle

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

theorem software_upper (memory : Memory) (frame : Frame) (a b : BitVec 64)
    (output reference middle : Reference) (digits : DigitHomes memory frame a b)
    (middleSlot : frame.locals[4]? = some (.bytes .word64 middle))
    (middleRead : read memory middle 8 1 = .ok (numberBytes (softwareMiddle a b).toNat 8))
    (slot : frame.locals[5]? = some (.bytes .word64 reference))
    (writable : access memory reference 8 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write memory reference (numberBytes (softwareUpper a b).toNat 8) 1 = .ok after →
      read after reference 8 1 = .ok (numberBytes (softwareUpper a b).toNat 8) →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex 62
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex 53
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
        [.scalar (.i32 (a.setWidth 32))] memory = .ok (final, returned) ∧ post final returned := by
  obtain ⟨digit2, slot2, read2⟩ := digits 2
  obtain ⟨after, stored, written, loaded⟩ := step_store_numeric_local
    (body := wordBody) (pc := 61)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]) (rest := [])
    .word64 (.i64 (softwareUpper a b)) (softwareUpper a b).toNat rfl slot writable
  have done := continuation after written loaded
  have found : Extracted.program[wordIndex]? = some wordBody := by rfl
  have load2 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word32 (.i32 ((b >>> 32).setWidth 32))
    ((b >>> 32).setWidth 32).toNat rfl slot2 read2
  have load4 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := wordBody)
    (args := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)])
    (pc := pc) (stack := stack) .word64 (.i64 (softwareMiddle a b))
    (softwareMiddle a b).toNat rfl middleSlot middleRead
  iterate 8
    apply run_next_exists post found (by rfl)
    first
    | exact load2 _ _
    | exact load4 _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simpa only [softwareUpper, digitLow, digitHigh, BitVec.zeroExtend] using stored
  exact done

#print axioms software_upper
end UInt256Proof.Multiply.Safety
