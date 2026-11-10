import UInt256.Safety.LocalCallSafety
import UInt256.Methods.Multiply.WordScalarSafety
import UInt256.Methods.Multiply.CountSafety

/-! Checked multiplication helper calls preserve private snapshots and return both product words. -/

namespace UInt256Proof.Multiply.Calls
open CIL.Safety UInt256Model.Safety

/-- The parent requires an actual checked widening-helper invocation. Scalar
    and hardware proofs supply this same contract at their respective gates. -/
def WordContract (program : CIL.Program) (wordIndex : Nat) : Prop :=
  ∀ (memory : Memory) (a b : BitVec 64) (output : Reference),
    memory.WellFormed → access memory output 8 1 true = .ok () →
    ∃ fuel final,
      invoke program fuel wordIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] memory =
        .ok (final, [.scalar (.i64 (highProduct a b))]) ∧
      final.WellFormed ∧ read final output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow memory.nextIdentity memory final ∧
      (∀ id, id < memory.nextIdentity → ∀ offset,
        id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
        final.cells id offset = memory.cells id offset)

/-- Compose a fetched widening call with its checked continuation. The low
    product initializes the selected private home; the high product is returned
    on the evaluation stack. All other initialized locals are preserved. -/
theorem run_word_call {program : CIL.Program} {wordIndex method pc : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack rest : List Value} {frame : Frame} {original entered current : Memory}
    {inputs outputs : List Reference} {known : Nat → Option (BitVec 64)} {kinds : List CIL.LocalKind}
    (contract : WordContract program wordIndex)
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (homes : CompleteWritableHomes entered original.nextIdentity kinds frame.locals)
    (index : Nat) (reference : Reference) (a b : BitVec 64)
    (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (ready : access current reference 8 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (found : program[method]? = some body)
    (fetched : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack current =
      .ok (.call wordIndex [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] rest current))
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord known index (lowProduct a b)) →
      WP (Execution (fun fuel => run program fuel method (pc + 1) args frame
        (.scalar (.i64 (highProduct a b)) :: rest) after)) (Function.uncurry post)) :
    WP (Execution (fun fuel => run program fuel method pc args frame stack current))
      (Function.uncurry post) := by
  have helper : WP (Execution (fun fuel => invoke program fuel wordIndex
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current))
      (fun (after, values) => values = [.scalar (.i64 (highProduct a b))] ∧
        after.WellFormed ∧
        read after reference 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
        AccessBelow current.nextIdentity current after ∧
        (∀ id, id < current.nextIdentity → ∀ offset,
          id ≠ reference.allocation ∨ offset < reference.offset ∨
            reference.offset + 8 ≤ offset →
          after.cells id offset = current.cells id offset)) := by
    obtain ⟨fuel, after, invoked, result⟩ :=
      contract current a b reference state.call.1.1 ready
    exact ⟨fuel, (after, [.scalar (.i64 (highProduct a b))]), invoked, rfl, result⟩
  have framed := helper.frame (initial := (current, []))
    (assertion := fun result => FrameInvariants program current result.1 ∧
      current.nextIdentity ≤ result.1.nextIdentity)
    ⟨FrameInvariants.refl program state.call.1.1, Nat.le_refl _⟩
    (by
      rintro fuel ⟨after, values⟩ invoked _
      exact ⟨call_frame_invariants found fetched stepped state.call.1.1 invoked,
        (invoke_preserves_caller_allocations program fuel wordIndex _ values
          current after invoked).next⟩)
  apply WP.call found fetched stepped framed
  intro after values callResult
  obtain ⟨⟨rfl, _, loaded, authority, outside⟩, invariants, grows⟩ := callResult
  have updated := state.after_word_call originalCall homes invariants grows
    index reference (lowProduct a b) slot loaded authority
    (fun id old different offset => outside id old offset (Or.inl different))
  simpa only [List.cons_append, List.nil_append] using continuation after updated

#print axioms run_word_call
end UInt256Proof.Multiply.Calls
namespace UInt256Proof.Multiply.Calls
open CIL.Safety UInt256Model.Safety

theorem widening_local_effect {program : CIL.Program} {wordIndex : Nat} (contract : WordContract program wordIndex) (current : Memory) (a b : BitVec 64)
    (wf : current.WellFormed) (reference : Reference)
    (ready : access current reference 8 1 true = .ok ()) :
    ∃ fuel after,
      invoke program fuel wordIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current =
        .ok (after, [.scalar (.i64 (highProduct a b))]) ∧
      after.WellFormed ∧ read after reference 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow current.nextIdentity current after ∧
      (∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
        after.cells id offset = current.cells id offset) := by
  obtain ⟨fuel, after, ran, valid, readback, access, outside⟩ := contract current a b reference wf ready
  exact ⟨fuel, after, ran, valid, readback, access, fun id old different offset =>
    outside id old offset (Or.inl different)⟩

theorem counting_local_effect (profile : CIL.FeatureProfile) (program : CIL.Program) (countIndex : Nat)
    (found : program[countIndex]? = some (CountSafety.body profile)) {current : Memory} {frame : Frame} {known : Nat → Option (BitVec 64)}
    (snapshots : WordSnapshots current frame.locals known) (wf : current.WellFormed)
    (index : Nat) (a b count : BitVec 64) (initialized : known index = some count)
    (reference : Reference) (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (ready : access current reference 8 1 true = .ok ()) :
    ∃ fuel after,
      invoke program fuel countIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current =
        .ok (after, [.scalar (.i64 (a + b))]) ∧
      after.WellFormed ∧ read after reference 8 1 = .ok (numberBytes (countCarry a b count).toNat 8) ∧
      AccessBelow current.nextIdentity current after ∧
      (∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
        after.cells id offset = current.cells id offset) := by
  obtain ⟨home, same, readable⟩ := snapshots index count initialized
  rw [slot] at same
  cases same
  obtain ⟨fuel, after, ran, valid, readback, access, outside⟩ := CountSafety.count_carry_invoke profile program countIndex found current a b count reference wf ready readable
  exact ⟨fuel, after, ran, valid, readback, access, fun id old different offset =>
    outside id old offset (Or.inl different)⟩

#print axioms widening_local_effect
#print axioms counting_local_effect
end UInt256Proof.Multiply.Calls
