import Extracted
import UInt256.Methods.Subtract.WrappingSafety
import CIL.Safety.WordFrameSetup
import CIL.Safety.ReturnMemory
import CIL.Safety.WordLocals

namespace UInt256Proof.Subtract.FixtureBorrowAlternative
open CIL.Safety UInt256Proof.Subtract.Safety

/-- The fixture keeps `a - b` in a word local and adds the two borrow indicators. -/
def alternativeWord (a b c : BitVec 64) : BitVec 64 :=
  (if a < b then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) +
    (if a - b < c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)

/-- Effects in order: local `a - b`, the difference word, then the borrow word. -/
theorem alternative_run (a b c : BitVec 64) (borrow output home : Reference)
    (activation : Nat) (locals : List LocalSlot) (owned : List Nat) (arguments : List (Nat × LocalSlot))
    (entered middle stored final : Memory)
    (slot : locals[0]? = some (.bytes .word64 home))
    (middleBorrow : form middle borrow = .ok borrow) (middleOutput : form middle output = .ok output)
    (storedBorrow : form stored borrow = .ok borrow)
    (localWrite : storeLocal entered (.bytes .word64 home) (.scalar (.i64 (a - b))) =
      .ok (.bytes .word64 home, middle))
    (middleLocal : read middle home 8 1 = .ok (numberBytes (a - b).toNat 8))
    (storedLocal : read stored home 8 1 = .ok (numberBytes (a - b).toNat 8))
    (beforeRead : loadValue middle (.address borrow) 8 = .ok (.i64 c))
    (afterRead : loadValue stored (.address borrow) 8 = .ok (.i64 c))
    (resultWrite : write middle output (numberBytes (a - b - c).toNat 8) 1 = .ok stored)
    (borrowWrite : write stored borrow (numberBytes (alternativeWord a b c).toNat 8) 1 = .ok final) :
    run Extracted.program (Extracted.subtractWithBorrowBody.code.length + 1)
      Extracted.subtractWithBorrowIndex 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrow), .reference (.address output)]
      ⟨activation, locals, owned, arguments⟩ [] entered =
        .ok (leaveFrame ⟨activation, locals, owned, arguments⟩ final, []) := by
  have unchanged : locals.set 0 (.bytes .word64 home) = locals := by
    apply List.ext_getElem?
    intro other
    by_cases same : 0 = other
    · subst other
      simp only [List.getElem?_set_self', slot]
      rfl
    · simp only [List.getElem?_set_ne same]
  have middleLoad := load_local_word64_of_read middleLocal
  have storedLoad := load_local_word64_of_read storedLocal
  simp [alternativeWord, BitVec.toNat_add] at borrowWrite
  simp [BitVec.toNat_sub] at resultWrite
  simp only [cil_code]
  repeat' first
    | (apply Eq.trans
       · apply run_next
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [cil_code, step, checkedValue, numericValue, formValue,
               middleBorrow, middleOutput, storedBorrow, slot, localWrite, unchanged, middleLoad, storedLoad,
               beforeRead, afterRead, pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary,
               instruction, storeValue, referenceAt, resultWrite, borrowWrite, checkedAt,
               Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           exact ⟨rfl, rfl, rfl, rfl⟩)
    | (solve
       | rw [run]
         simp (config := { implicitDefEqProofs := false })
           [cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
  simp [run, cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem alternative_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    alternativeWord a b c = UInt256Proof.borrow a b c :=
  UInt256Proof.borrow_alternative_expression a b c incoming

/-- The helper's word local is a fresh allocation released on return, so only
    the caller's two words change below the entry watermark. -/
theorem alternative_contract : BorrowHelperContract := by
  intro a b c borrowRef output memory wellFormed incoming readable writable outputWritable disjoint
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  let args : List Value :=
    [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
  obtain ⟨frame, entered, setup, homes, below, _⟩ := word_frame_setup Extracted.subtractWithBorrowBody
    [some 0] (by rfl) (by rfl) (by rfl) (by rfl) memory args wellFormed
  obtain ⟨home, slot, fresh, -, homeWritable⟩ := homes.word_at 0 0 rfl
  obtain ⟨_, borrowPresent, _, _⟩ := access_within_allocation _ _ _ _ _ writable
  obtain ⟨_, outputPresent, _, _⟩ := access_within_allocation _ _ _ _ _ outputWritable
  have borrowOld := (wellFormed.1 _ _ borrowPresent).1
  have outputOld := (wellFormed.1 _ _ outputPresent).1
  have homeBorrow : borrowRef.allocation ≠ home.allocation := Nat.ne_of_lt (Nat.lt_of_lt_of_le borrowOld fresh)
  have homeOutput : home.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld fresh))
  have enteredReadable : read entered borrowRef 8 1 = .ok (numberBytes c.toNat 8) := by
    rw [below.read borrowRef borrowOld]; exact readable
  have enteredBorrowW : access entered borrowRef 8 1 true = .ok () := by
    rw [below.access borrowRef borrowOld]; exact writable
  have enteredOutputW : access entered output 8 1 true = .ok () := by
    rw [below.access output outputOld]; exact outputWritable
  obtain ⟨middle, localWritten, localStored, middleLocal, _⟩ := store_local_word64 (a - b) homeWritable
  have middleReadable := write_preserves_disjoint_read localWritten enteredReadable (Or.inl homeBorrow)
  obtain ⟨_, borrowAuthority⟩ := access_requirements enteredBorrowW
  obtain ⟨_, outputAuthority⟩ := access_requirements enteredOutputW
  have middleBorrowW := (borrowAuthority.after_write localWritten).access
  have middleOutputW := (outputAuthority.after_write localWritten).access
  obtain ⟨stored, resultWrite⟩ := write_succeeds (bytes := numberBytes (a - b - c).toNat 8)
    (by simpa only [length] using middleOutputW)
  have storedReadable := write_preserves_disjoint_read resultWrite middleReadable
    (by simpa only [WordsDisjoint, length] using disjoint)
  have storedLocal := write_preserves_disjoint_read resultWrite middleLocal (Or.inl homeOutput)
  have storedBorrowW := ((borrowAuthority.after_write localWritten).after_write resultWrite).access
  obtain ⟨final, borrowWrite⟩ := write_succeeds (bytes := numberBytes (alternativeWord a b c).toNat 8)
    (by simpa only [length] using storedBorrowW)
  have owned := enterFrame_fresh _ _ _ _ _ setup
  obtain ⟨activation, locals, ownedIds, arguments⟩ := frame
  have run := alternative_run a b c borrowRef output home activation locals ownedIds arguments
    entered middle stored final slot (access_reference_valid _ _ _ _ _ middleBorrowW)
    (access_reference_valid _ _ _ _ _ middleOutputW) (access_reference_valid _ _ _ _ _ storedBorrowW)
    localStored middleLocal storedLocal (load_word64_of_read middleReadable)
    (load_word64_of_read storedReadable) resultWrite borrowWrite
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, checkedValue, numericValue, formValue, access_reference_valid _ _ _ _ _ writable,
      access_reference_valid _ _ _ _ _ outputWritable, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have invoked := invoke_of_run (by rfl) checked setup run
  have retained := leaveFrame_preserves_memory_below ⟨activation, locals, ownedIds, arguments⟩ final
    memory.nextIdentity (fun id member => (owned.2 id member).1)
  refine ⟨_, _, invoked, invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked, ?_, ?_,
    UInt256Proof.borrow_bound a b c, UInt256Proof.borrow_word_nat a b c incoming, ?_, ?_,
    fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩
  · rw [retained.read output outputOld]
    have readback : read stored output 8 1 = .ok (numberBytes (a - b - c).toNat 8) := by
      simpa only [length] using write_readback _ _ _ _ _ resultWrite
    apply write_preserves_disjoint_read borrowWrite readback
    rcases disjoint with distinct | before | after
    · exact Or.inl (Ne.symm distinct)
    · exact Or.inr (Or.inr (by simpa only [length] using before))
    · exact Or.inr (Or.inl (by simpa only [length] using after))
  · rw [retained.read borrowRef borrowOld]
    have readback := write_readback _ _ _ _ _ borrowWrite
    simpa only [length, alternative_correct a b c incoming] using readback
  · intro id offset old outsideBorrow outsideOutput
    rw [retained.cells id old offset, write_word_outside borrowWrite id offset outsideBorrow,
      write_word_outside resultWrite id offset outsideOutput,
      write_word_outside localWritten id offset (Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le old fresh))),
      below.cells id old offset]
  · exact below.accessBelow.trans ((write_preserves_access_below localWritten _).trans
      ((write_preserves_access_below resultWrite _).trans
        ((write_preserves_access_below borrowWrite _).trans retained.accessBelow)))

theorem correctness : UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program 0 :=
  checked_wrapping_contract alternative_contract

#print axioms correctness
end UInt256Proof.Subtract.FixtureBorrowAlternative
