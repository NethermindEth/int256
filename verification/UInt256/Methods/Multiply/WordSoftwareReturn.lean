import UInt256.Methods.Multiply.WordSoftwareOutput

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
