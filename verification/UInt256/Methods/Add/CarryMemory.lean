import Extracted
import CIL.Safety.WordLocals
import CIL.Safety.StepComposition
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow

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

namespace UInt256Proof.Safety

open CIL.Safety

/-- Ordinary access and local-ownership conditions suffice for the actual body.
    The two caller references may overlap: the input carry is read before stores. -/
theorem carry_body_succeeds (a b c : BitVec 64) (carry output first second : Reference)
    (frame : Frame) (memory : Memory)
    (locals : frame.locals = [.bytes .word64 first, .bytes .word64 second])
    (distinct : first.allocation ≠ second.allocation)
    (privateFirst : carry.allocation ≠ first.allocation)
    (privateSecond : carry.allocation ≠ second.allocation)
    (firstWritable : access memory first 8 1 true = .ok ())
    (secondWritable : access memory second 8 1 true = .ok ())
    (carryReadable : read memory carry 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carry 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ()) :
    ∃ stored,
      run Extracted.program (Extracted.addWithCarryBody.code.length + 1)
        Extracted.addWithCarryIndex 0
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
        frame [] memory = .ok (leaveFrame frame stored, []) ∧
      read stored output 8 1 = .ok (numberBytes (a + b + c).toNat 8) ∧
      (WordsDisjoint carry output → read stored carry 8 1 = .ok (numberBytes (carryWord a b c).toNat 8)) ∧
      (∀ id offset, id ≠ first.allocation → id ≠ second.allocation →
        OutsideWord carry id offset → OutsideWord output id offset →
        stored.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory stored := by
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨secondAllocation, secondAccess⟩ := access_requirements secondWritable
  obtain ⟨carryAllocation, carryAccess⟩ := access_requirements carryWritable
  obtain ⟨outputAllocation, outputAccess⟩ := access_requirements outputWritable
  obtain ⟨m1, w0, s0, firstRead, firstLoad⟩ := store_local_word64 (a + b) firstWritable
  have readCarry := write_preserves_disjoint_read w0 carryReadable (Or.inl privateFirst)
  obtain ⟨m2, w1, s1, secondRead, secondLoad⟩ :=
    store_local_word64 (a + b + c) (secondAccess.after_write w0).access
  have retainedFirst := write_preserves_disjoint_read w1 firstRead (Or.inl distinct)
  have carry1 := (carryAccess.after_write w0).access
  have carry2 := ((carryAccess.after_write w0).after_write w1).access
  obtain ⟨m3, wc⟩ := write_succeeds (bytes := numberBytes (carryWord a b c).toNat 8)
    (by simpa only [length] using carry2)
  have retainedSecond := write_preserves_disjoint_read wc secondRead (Or.inl (Ne.symm privateSecond))
  have output3 := (((outputAccess.after_write w0).after_write w1).after_write wc).access
  obtain ⟨m4, wo⟩ := write_succeeds (bytes := numberBytes (a + b + c).toNat 8)
    (by simpa only [length] using output3)
  refine ⟨m4, carry_run_of_memory_steps a b c carry output first second frame memory m1 m2 m3 m4
    locals s0 s1 firstLoad (load_word64_of_read readCarry)
    (load_local_word64_of_read retainedFirst) secondLoad
    (load_local_word64_of_read retainedSecond)
    (access_reference_valid _ _ _ _ _ carry1) (access_reference_valid _ _ _ _ _ carry2)
    (access_reference_valid _ _ _ _ _ output3) wc wo, ?_, ?_, ?_, ?_⟩
  · simpa only [length] using write_readback _ _ _ _ _ wo
  · intro disjoint
    have carryRead : read m3 carry 8 1 = .ok (numberBytes (carryWord a b c).toNat 8) := by
      simpa only [length] using write_readback _ _ _ _ _ wc
    exact write_preserves_disjoint_read wo carryRead (by simpa only [WordsDisjoint, length] using disjoint)
  · intro id offset notFirst notSecond outsideCarry outsideOutput
    rw [write_word_outside wo id offset outsideOutput,
      write_word_outside wc id offset outsideCarry,
      write_word_outside w1 id offset (Or.inl notSecond),
      write_word_outside w0 id offset (Or.inl notFirst)]

  · exact (write_preserves_access_below w0 memory.nextIdentity).trans
      ((write_preserves_access_below w1 memory.nextIdentity).trans
        ((write_preserves_access_below wc memory.nextIdentity).trans
          (write_preserves_access_below wo memory.nextIdentity)))

#print axioms carry_body_succeeds

end UInt256Proof.Safety
