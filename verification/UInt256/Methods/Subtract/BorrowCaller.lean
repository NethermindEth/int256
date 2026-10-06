import UInt256.Methods.Subtract.BorrowSafety
import UInt256.Safety.PrivateCalls
import CIL.Safety.CallComposition

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
