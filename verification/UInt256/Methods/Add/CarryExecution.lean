import Extracted
import CIL.Safety.WordLocals
import CIL.Safety.StepComposition

namespace UInt256Proof.Safety

open CIL.Safety

def carryWord (a b c : BitVec 64) : BitVec 64 :=
  ((if a + b < a then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64) +
  ((if a + b + c < a + b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

/-- Symbolic execution of the extracted body, with explicit checked memory
    transitions. Access and preservation lemmas discharge these premises. -/
theorem carry_run_of_memory_steps (a b c : BitVec 64) (carry output first second : Reference)
    (frame : Frame) (m0 m1 m2 m3 m4 : Memory)
    (locals : frame.locals = [.bytes .word64 first, .bytes .word64 second])
    (s0 : storeLocal m0 (.bytes .word64 first) (.scalar (.i64 (a + b))) =
      .ok (.bytes .word64 first, m1))
    (s1 : storeLocal m1 (.bytes .word64 second) (.scalar (.i64 (a + b + c))) =
      .ok (.bytes .word64 second, m2))
    (r0 : loadLocal m1 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))))
    (rc : loadValue m1 (.address carry) 8 = .ok (.i64 c))
    (r1 : loadLocal m2 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))))
    (r2 : loadLocal m2 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))))
    (r3 : loadLocal m3 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))))
    (fc1 : form m1 carry = .ok carry) (fc2 : form m2 carry = .ok carry)
    (fo3 : form m3 output = .ok output)
    (wc : write m2 carry (numberBytes (carryWord a b c).toNat 8) 1 = .ok m3)
    (wo : write m3 output (numberBytes (a + b + c).toNat 8) 1 = .ok m4) :
    run Extracted.program (Extracted.addWithCarryBody.code.length + 1)
      Extracted.addWithCarryIndex 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
      frame [] m0 = .ok (leaveFrame frame m4, []) := by
  simp [carryWord, BitVec.toNat_add] at wc
  simp [BitVec.toNat_add] at wo
  simp only [cil_code]
  repeat'
    first
    | apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, locals, s0, s1, r0, rc, r1, r2, r3,
              checkedValue, numericValue, formValue, fc1, fc2, fo3,
              pureArity, scalars, CIL.step, CIL.binary, instruction, storeValue,
              referenceAt, wc, wo, checkedAt, Except.mapError,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [cil_code, step, leaveFrame,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms carry_run_of_memory_steps

end UInt256Proof.Safety
