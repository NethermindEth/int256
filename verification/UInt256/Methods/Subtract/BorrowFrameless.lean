import UInt256.Methods.Subtract.BorrowPost

namespace UInt256Proof.Subtract.Safety
open CIL.Safety

/-- A local-free borrow body with a proved run and a borrow word equal to the
    mathematical borrow for incoming borrows of at most one. -/
theorem borrow_contract_of_run (bw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) (runs : BorrowRun bw)
    (correct : ∀ a b c : BitVec 64, c.toNat ≤ 1 → bw a b c = UInt256Proof.borrow a b c) :
    BorrowHelperContract := by
  intro a b c borrowRef output memory wellFormed incoming readable writable outputWritable disjoint
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨allocation, authority⟩ := access_requirements writable
  obtain ⟨stored, resultWrite⟩ := write_succeeds (bytes := numberBytes (a - b - c).toNat 8)
    (by simpa only [length] using outputWritable)
  have retained := write_preserves_disjoint_read resultWrite readable
    (by simpa only [WordsDisjoint, length] using disjoint)
  have borrowWritable := (authority.after_write resultWrite).access
  obtain ⟨final, borrowWrite⟩ := write_succeeds (bytes := numberBytes (bw a b c).toNat 8)
    (by simpa only [length] using borrowWritable)
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fb := access_reference_valid _ _ _ _ _ writable
  have fo := access_reference_valid _ _ _ _ _ outputWritable
  have run := runs a b c borrowRef output frame memory stored final fb fo
    (access_reference_valid _ _ _ _ _ borrowWritable) (load_word64_of_read readable)
    (load_word64_of_read retained) resultWrite borrowWrite
  simp only [leaveFrame, frame, List.foldl_nil] at run
  have invoked : invoke Extracted.program (Extracted.subtractWithBorrowBody.code.length + 1)
      Extracted.subtractWithBorrowIndex
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
      memory = .ok (final, []) := by
    simpa [invoke, cil_code, enterFrame, makeLocals, makeArgumentHomes, makeParameterHomes, frame, checkedValue,
      numericValue, formValue, fb, fo, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure] using run
  refine ⟨_, final, invoked, invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked,
    ?_, ?_, UInt256Proof.borrow_bound a b c, UInt256Proof.borrow_word_nat a b c incoming, ?_,
    (write_preserves_access_below resultWrite memory.nextIdentity).trans
      (write_preserves_access_below borrowWrite memory.nextIdentity),
    fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩
  · have readback : read stored output 8 1 = .ok (numberBytes (a - b - c).toNat 8) := by
      simpa only [length] using write_readback _ _ _ _ _ resultWrite
    apply write_preserves_disjoint_read borrowWrite readback
    rcases disjoint with distinct | before | after
    · exact Or.inl (Ne.symm distinct)
    · exact Or.inr (Or.inr (by simpa only [length] using before))
    · exact Or.inr (Or.inl (by simpa only [length] using after))
  · have readback := write_readback _ _ _ _ _ borrowWrite
    simpa only [length, correct a b c incoming] using readback
  · intro id offset _ outsideBorrow outsideOutput
    rw [write_word_outside borrowWrite id offset outsideBorrow,
      write_word_outside resultWrite id offset outsideOutput]

#print axioms borrow_contract_of_run
end UInt256Proof.Subtract.Safety
