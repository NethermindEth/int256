import UInt256.Methods.Subtract.Bindings
import CIL.Safety.StepComposition
import CIL.Safety.SymbolicExecution
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow
import CIL.Safety.ExecutionStaticWorld
import UInt256.Arithmetic.Borrow
import UInt256.Safety.PrivateCalls

namespace UInt256Proof.Subtract.Safety
open CIL.Safety

/-- The production borrow word: `a < b`, or an incoming borrow when `a = b`. -/
def borrowWord (a b c : BitVec 64) : BitVec 64 :=
  (if a < b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64 |||
    (c &&& (if a = b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

theorem borrowWord_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    borrowWord a b c = UInt256Proof.borrow a b c := by
  simpa only [borrowWord, UInt256Proof.extend_subtract_choice] using
    UInt256Proof.borrow_expression a b c incoming

structure BorrowPost (a b c : BitVec 64) (borrowRef output : Reference) (before after : Memory) : Prop where
  wellFormed : after.WellFormed
  outputBytes : read after output 8 1 = .ok (numberBytes (a - b - c).toNat 8)
  borrowBytes : read after borrowRef 8 1 = .ok (numberBytes (UInt256Proof.borrow a b c).toNat 8)
  borrowBound : (UInt256Proof.borrow a b c).toNat ≤ 1
  arithmetic : a.toNat + 2^64 * (UInt256Proof.borrow a b c).toNat = b.toNat + c.toNat + (a - b - c).toNat
  footprint : ∀ id offset, id < before.nextIdentity → OutsideWord borrowRef id offset → OutsideWord output id offset →
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

/-- The parent needs only a checked borrow-helper invocation; each extraction proves
    this from its own helper body. Simultaneous readback requires disjoint words. -/
def BorrowHelperContract : Prop :=
  ∀ (a b c : BitVec 64) (borrowRef output : Reference) (memory : Memory),
    memory.WellFormed → c.toNat ≤ 1 →
    read memory borrowRef 8 1 = .ok (numberBytes c.toNat 8) →
    access memory borrowRef 8 1 true = .ok () →
    access memory output 8 1 true = .ok () →
    WordsDisjoint borrowRef output →
    ∃ fuel final,
      invoke Extracted.program fuel Extracted.subtractWithBorrowIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowRef), .reference (.address output)]
        memory = .ok (final, []) ∧ BorrowPost a b c borrowRef output memory final

/-- Execution of a local-free borrow body whose only memory effects are, in order,
    the difference write and the borrow write `bw`. -/
def BorrowRun (bw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ (a b c : BitVec 64) (borrow output : Reference) (frame : Frame) (memory stored final : Memory),
    form memory borrow = .ok borrow → form memory output = .ok output → form stored borrow = .ok borrow →
    loadValue memory (.address borrow) 8 = .ok (.i64 c) → loadValue stored (.address borrow) 8 = .ok (.i64 c) →
    write memory output (numberBytes (a - b - c).toNat 8) 1 = .ok stored →
    write stored borrow (numberBytes (bw a b c).toNat 8) 1 = .ok final →
    run Extracted.program (Extracted.subtractWithBorrowBody.code.length + 1)
      Extracted.subtractWithBorrowIndex 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrow), .reference (.address output)]
      frame [] memory = .ok (leaveFrame frame final, [])

set_option hygiene false in
/-- Prove `BorrowRun` by executing every fetched instruction, including calls to
    frameless pure helpers; `normalize` puts the borrow write in evaluated form. -/
macro "borrow_run_steps " "[" normalize:term,* "]" : tactic => `(tactic| (
  intro a b c borrow output frame memory stored final borrowFormed outputFormed borrowStored beforeRead
    afterRead resultWrite borrowWrite
  simp [$[$normalize:term],*] at borrowWrite
  simp [BitVec.toNat_sub] at resultWrite
  simp only [cil_code]
  repeat' first
    | (apply Eq.trans
       · apply run_next
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [cil_code, step, checkedValue, numericValue, formValue, borrowFormed, outputFormed,
               borrowStored, beforeRead, afterRead, pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary,
               instruction, storeValue, referenceAt, resultWrite, borrowWrite, checkedAt,
               Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           exact ⟨rfl, rfl, rfl, rfl⟩)
    | (apply run_call_of_invoke
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [cil_code, step, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind,
           Pure.pure, Except.pure]
         exact ⟨rfl, rfl, rfl, rfl⟩
       · cil_checked_steps
       simp only [List.append_nil, List.cons_append, List.nil_append, Nat.reduceAdd, leaveFrame, List.foldl_nil])
    | (solve
       | rw [run]
         simp (config := { implicitDefEqProofs := false })
           [cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
  simp [run, cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]))

#print axioms borrowWord_correct
#print axioms BorrowPost.output_load
#print axioms BorrowPost.borrow_load
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
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  exact post.footprint _ _ (call.1.1.1 _ _ present).1
    (Or.inl (separate reference member).1) (Or.inl (separate reference member).2)

theorem BorrowPost.private_input_bytes {a b c : BitVec 64} {borrowRef output : Reference}
    {before after : Memory} (post : BorrowPost a b c borrowRef output before after)
    (reference : Reference) (old : reference.allocation < before.nextIdentity)
    (notBorrow : reference.allocation ≠ borrowRef.allocation)
    (notOutput : reference.allocation ≠ output.allocation) :
    (fun offset => (after.cells reference.allocation offset).bits) =
      (fun offset => (before.cells reference.allocation offset).bits) := by
  funext offset
  rw [post.footprint _ _ old (Or.inl notBorrow) (Or.inl notOutput)]

theorem BorrowPost.private_input_field {a b c : BitVec 64} {borrowRef output : Reference}
    {before after : Memory} (post : BorrowPost a b c borrowRef output before after)
    {inputs outputs : List Reference} (call : CallingConditions Extracted.program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ borrowRef.allocation ∧ reference.allocation ≠ output.allocation)
    {reference : Reference} (member : reference ∈ inputs) (index : Fin 4) (rest : List Value) :
    instruction (.fieldAt (8 * index.val) 8) (.reference (.address reference) :: rest) after =
      .ok (after, .scalar (.i64 (inputLimb before reference index)) :: rest) := by
  rw [(post.private_calling_conditions call separate).input_field_instruction member index rest]
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  simp only [inputLimb, post.private_input_bytes reference (call.1.1.1 _ _ present).1
    (separate reference member).1 (separate reference member).2]

theorem run_borrow_call (contract : BorrowHelperContract) {method pc : Nat} {body : CIL.Method} {op : CIL.Op}
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
  obtain ⟨childFuel, stored, invoked, guarantees⟩ := contract a b c borrowRef output updated
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
