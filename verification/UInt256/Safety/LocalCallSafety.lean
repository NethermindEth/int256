import UInt256.Safety.PrivateWordAccess
import CIL.Safety.WeakestPrecondition

/-! Checked local-writing calls carry the helper's low word and returned high word into a suffix. -/

namespace UInt256Model.Safety
open CIL.Safety

/-- Execute two initialized local loads, pass a writable private home to an
    actually proved call, then store its returned word. Instruction identities
    and both memory effects are premises checked by each caller. -/
theorem run_local_word_call {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method}
    {args rest : List Value} {frame : Frame} {original entered current : Memory}
    {inputs outputs : List Reference} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity body.localKinds frame.locals)
    (left right target result : Nat) (a b stored returned : BitVec 64)
    (leftKnown : known left = some a) (rightKnown : known right = some b)
    (targetKind : body.localKinds[target]? = some .word64)
    (resultKind : body.localKinds[result]? = some .word64)
    (found : program[method]? = some body)
    (code0 : body.code[pc]? = some (.local left))
    (code1 : body.code[pc + 1]? = some (.local right))
    (code2 : body.code[pc + 2]? = some (.localAddr target))
    (code3 : body.code[pc + 3]? = some (.call callee 3))
    (code4 : body.code[pc + 4]? = some (.setLocal result))
    (effect : ∀ reference, frame.locals[target]? = some (.bytes .word64 reference) →
      access current reference 8 1 true = .ok () →
      ∃ fuel after,
        invoke program fuel callee [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current =
          .ok (after, [.scalar (.i64 returned)]) ∧
        after.WellFormed ∧ read after reference 8 1 = .ok (numberBytes stored.toNat 8) ∧
        AccessBelow current.nextIdentity current after ∧
        (∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
          after.cells id offset = current.cells id offset))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord (rememberWord known target stored) result returned) →
      WP (Execution (fun fuel => run program fuel method (pc + 5) args frame rest after))
        (Function.uncurry post)) :
    WP (Execution (fun fuel => run program fuel method pc args frame rest current))
      (Function.uncurry post) := by
  obtain ⟨reference, slot, ready, formed⟩ := state.home enteredWF homes target targetKind
  apply WP.step found code0 (state.snapshots.load a leftKnown)
  apply WP.step found code1 (state.snapshots.load b rightKnown)
  apply WP.step found code2 (by cil_checked_step [slot, formed, localAddress])
  have called : step body (.call callee 3) (pc + 3) args frame
      (.reference (.address reference) :: .scalar (.i64 b) :: .scalar (.i64 a) :: rest)
      current = .ok (.call callee
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] rest current) := by
    cil_checked_step [formed]
  have helper : WP (Execution (fun fuel => invoke program fuel callee
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current))
      (fun (after, values) => values = [.scalar (.i64 returned)] ∧
        after.WellFormed ∧ read after reference 8 1 = .ok (numberBytes stored.toNat 8) ∧
        AccessBelow current.nextIdentity current after ∧
        (∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
          after.cells id offset = current.cells id offset)) := by
    obtain ⟨fuel, after, invoked, result⟩ := effect reference slot ready
    exact ⟨fuel, (after, [.scalar (.i64 returned)]), invoked, rfl, result⟩
  apply WP.call_framed found code3 called state.call.1.1 helper
  intro after values callResult invariants allocations
  obtain ⟨rfl, _, loaded, authority, outside⟩ := callResult
  have updated := state.after_word_call originalCall homes invariants allocations.next
    target reference stored slot loaded authority outside
  obtain ⟨prepared, written, preparedState⟩ := updated.store enteredWF homes result resultKind returned
    (pc + 4) args rest (body := body)
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.cons_append, List.nil_append] using
    WP.step found code4 written (continuation prepared preparedState)

end UInt256Model.Safety
