import Extracted
import CIL.Safety.StepComposition
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow
import CIL.Safety.ExecutionStaticWorld
import UInt256.Arithmetic.Borrow
import UInt256.Safety.PrivateCalls
import CIL.Safety.CallComposition

namespace UInt256Proof.Subtract.Safety
open CIL.Safety

def borrowWord (a b c : BitVec 64) : BitVec 64 :=
  (if a < b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64 |||
    (c &&& (if a = b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

theorem borrowWord_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    borrowWord a b c = UInt256Proof.borrow a b c := by
  simpa only [borrowWord, UInt256Proof.extend_subtract_choice] using
    UInt256Proof.borrow_expression a b c incoming

theorem borrow_run (a b c : BitVec 64) (borrow output : Reference) (frame : Frame)
    (memory stored final : Memory)
    (borrowFormed : form memory borrow = .ok borrow) (outputFormed : form memory output = .ok output)
    (borrowStored : form stored borrow = .ok borrow)
    (beforeRead : loadValue memory (.address borrow) 8 = .ok (.i64 c))
    (afterRead : loadValue stored (.address borrow) 8 = .ok (.i64 c))
    (resultWrite : write memory output (numberBytes (a - b - c).toNat 8) 1 = .ok stored)
    (borrowWrite : write stored borrow (numberBytes (borrowWord a b c).toNat 8) 1 = .ok final) :
    run Extracted.program (Extracted.subtractWithBorrowBody.code.length + 1)
      Extracted.subtractWithBorrowIndex 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrow), .reference (.address output)]
      frame [] memory = .ok (leaveFrame frame final, []) := by
  simp [borrowWord, BitVec.toNat_or, BitVec.toNat_and] at borrowWrite
  simp [BitVec.toNat_sub] at resultWrite
  simp only [cil_code]
  repeat' first
    | (apply Eq.trans
       · apply run_next
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [cil_code, step, checkedValue, numericValue, formValue, borrowFormed, outputFormed,
               borrowStored, beforeRead, afterRead, pureArity, scalars, CIL.step.eq_def, CIL.binary,
               instruction, storeValue, referenceAt, resultWrite, borrowWrite, checkedAt,
               Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           exact ⟨rfl, rfl, rfl, rfl⟩)
    | (solve
       | rw [run]
         simp (config := { implicitDefEqProofs := false })
           [cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])

structure BorrowPost (a b c : BitVec 64) (borrowRef output : Reference) (before after : Memory) : Prop where
  wellFormed : after.WellFormed
  outputBytes : read after output 8 1 = .ok (numberBytes (a - b - c).toNat 8)
  borrowBytes : read after borrowRef 8 1 = .ok (numberBytes (UInt256Proof.borrow a b c).toNat 8)
  borrowBound : (UInt256Proof.borrow a b c).toNat ≤ 1
  arithmetic : a.toNat + 2^64 * (UInt256Proof.borrow a b c).toNat = b.toNat + c.toNat + (a - b - c).toNat
  footprint : ∀ id offset, OutsideWord borrowRef id offset → OutsideWord output id offset →
    after.cells id offset = before.cells id offset
  access : AccessBelow before.nextIdentity before after
  staticWorld : StaticWorldValid (programStaticDescriptors Extracted.program) before →
    StaticWorldValid (programStaticDescriptors Extracted.program) after

theorem BorrowPost.output_load {a b c : BitVec 64} {borrowRef output : Reference} {before after : Memory}
    (post : BorrowPost a b c borrowRef output before after) :
    loadValue after (.address output) 8 = .ok (.i64 (a - b - c)) := load_word64_of_read post.outputBytes

theorem BorrowPost.borrow_load {a b c : BitVec 64} {borrowRef output : Reference} {before after : Memory}
    (post : BorrowPost a b c borrowRef output before after) :
    loadValue after (.address borrowRef) 8 = .ok (.i64 (UInt256Proof.borrow a b c)) :=
  load_word64_of_read post.borrowBytes

theorem borrow_checked_contract (a b c : BitVec 64) (borrowRef output : Reference) (memory : Memory)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (readable : read memory borrowRef 8 1 = .ok (numberBytes c.toNat 8))
    (writable : access memory borrowRef 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowRef output) :
    ∃ fuel final,
      invoke Extracted.program fuel Extracted.subtractWithBorrowIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
        memory = .ok (final, []) ∧ BorrowPost a b c borrowRef output memory final := by
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨allocation, authority⟩ := access_requirements writable
  obtain ⟨stored, resultWrite⟩ := write_succeeds (bytes := numberBytes (a - b - c).toNat 8)
    (by simpa only [length] using outputWritable)
  have retained := write_preserves_disjoint_read resultWrite readable
    (by simpa only [WordsDisjoint, length] using disjoint)
  have borrowWritable := (authority.after_write resultWrite).access
  obtain ⟨final, borrowWrite⟩ := write_succeeds (bytes := numberBytes (borrowWord a b c).toNat 8)
    (by simpa only [length] using borrowWritable)
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fb := access_reference_valid _ _ _ _ _ writable
  have fo := access_reference_valid _ _ _ _ _ outputWritable
  have run := borrow_run a b c borrowRef output frame memory stored final fb fo
    (access_reference_valid _ _ _ _ _ borrowWritable) (load_word64_of_read readable)
    (load_word64_of_read retained) resultWrite borrowWrite
  simp only [leaveFrame, frame, List.foldl_nil] at run
  have invoked : invoke Extracted.program (Extracted.subtractWithBorrowBody.code.length + 1)
      Extracted.subtractWithBorrowIndex
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
      memory = .ok (final, []) := by
    simpa [invoke, cil_code, enterFrame, makeLocals, makeArgumentHomes, frame, checkedValue,
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
    simpa only [length, borrowWord_correct a b c incoming] using readback
  · intro id offset outsideBorrow outsideOutput
    rw [write_word_outside borrowWrite id offset outsideBorrow,
      write_word_outside resultWrite id offset outsideOutput]

#print axioms borrowWord_correct
#print axioms borrow_run
#print axioms BorrowPost.output_load
#print axioms BorrowPost.borrow_load
#print axioms borrow_checked_contract
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

theorem BorrowPost.private_calling_conditions {a b c : BitVec 64} {borrowRef output : Reference}
    {before after : Memory} (post : BorrowPost a b c borrowRef output before after)
    {inputs outputs : List Reference} (call : CallingConditions Extracted.program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ borrowRef.allocation ∧ reference.allocation ≠ output.allocation) :
    CallingConditions Extracted.program after inputs outputs := by
  apply call.after_preserving_inputs post.wellFormed post.access (post.staticWorld call.2)
  intro reference member offset _
  exact post.footprint _ _ (Or.inl (separate reference member).1) (Or.inl (separate reference member).2)

theorem BorrowPost.private_input_bytes {a b c : BitVec 64} {borrowRef output : Reference}
    {before after : Memory} (post : BorrowPost a b c borrowRef output before after)
    (reference : Reference) (notBorrow : reference.allocation ≠ borrowRef.allocation)
    (notOutput : reference.allocation ≠ output.allocation) :
    (fun offset => (after.cells reference.allocation offset).bits) =
      (fun offset => (before.cells reference.allocation offset).bits) := by
  funext offset
  rw [post.footprint _ _ (Or.inl notBorrow) (Or.inl notOutput)]

theorem BorrowPost.private_input_field {a b c : BitVec 64} {borrowRef output : Reference}
    {before after : Memory} (post : BorrowPost a b c borrowRef output before after)
    {inputs outputs : List Reference} (call : CallingConditions Extracted.program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ borrowRef.allocation ∧ reference.allocation ≠ output.allocation)
    {reference : Reference} (member : reference ∈ inputs) (index : Fin 4) (rest : List Value) :
    instruction (.field index) (.reference (.address reference) :: rest) after =
      .ok (after, .scalar (.i64 (inputLimb before reference index)) :: rest) := by
  rw [(post.private_calling_conditions call separate).input_field_instruction member index rest]
  simp only [inputLimb, post.private_input_bytes reference (separate reference member).1
    (separate reference member).2]

theorem run_borrow_call {method pc : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack rest : List Value} {frame : Frame} {memory updated : Memory}
    (a b c : BitVec 64) (borrowRef output : Reference) (post : Memory → List Value → Prop)
    (methodFound : Extracted.program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call Extracted.subtractWithBorrowIndex
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)] rest updated))
    (wellFormed : updated.WellFormed) (incoming : c.toNat ≤ 1)
    (readable : read updated borrowRef 8 1 = .ok (numberBytes c.toNat 8))
    (writable : access updated borrowRef 8 1 true = .ok ())
    (outputWritable : access updated output 8 1 true = .ok ()) (disjoint : WordsDisjoint borrowRef output)
    (continuation : ∀ stored, BorrowPost a b c borrowRef output updated stored →
      ∃ fuel result values,
        run Extracted.program fuel method (pc + 1) args frame rest stored = .ok (result, values) ∧
        post result values) :
    ∃ fuel result values,
      run Extracted.program fuel method pc args frame stack memory = .ok (result, values) ∧ post result values := by
  obtain ⟨childFuel, stored, invoked, guarantees⟩ := borrow_checked_contract a b c borrowRef output updated
    wellFormed incoming readable writable outputWritable disjoint
  obtain ⟨parentFuel, result, values, resumed, satisfied⟩ := continuation stored guarantees
  obtain ⟨fuel, finished⟩ := run_call_exists methodFound instructionFound stepped
    ⟨childFuel, invoked⟩ ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, values, finished, satisfied⟩

#print axioms BorrowPost.private_calling_conditions
#print axioms BorrowPost.private_input_bytes
#print axioms BorrowPost.private_input_field
#print axioms run_borrow_call
end UInt256Proof.Subtract.Safety
