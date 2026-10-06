import UInt256.Methods.Shift.SafetyCount

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- All signed count branches either reach the zero write or select a bounded
    whole-limb count, retaining the caller memory and private-home authority. -/
theorem shift_count_dispatch (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (zero : ∀ after,
      ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 →
      (0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : BitVec 32) = 0) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run Extracted.program fuel shiftIndex (shiftPc 14) args frame [] after =
        .ok (final, returned) ∧ post final returned)
    (ready : ∀ whole reference after,
      whole < BitVec.ofNat 32 4 →
      (whole = count.sshiftRight 6 ∨
        (whole = 0 ∧ (count.sshiftRight 6).toInt < 0 ∧ count &&& (63 : BitVec 32) ≠ 0)) →
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes whole.toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned, run Extracted.program fuel shiftIndex (shiftPc 19) args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run Extracted.program fuel shiftIndex 0 args frame [] current =
      .ok (final, returned) ∧ post final returned := by
  apply shift_count_start boundary entered current inputs outputs frame args count argument
    call enteredWF homes authority post
  intro reference middle slot loaded preserved middleCall middleAuthority written
  have next := (write_extends_allocations _ _ _ _ _ written).next
  apply shift_count_guard false middle frame args (count.sshiftRight 6) reference slot loaded post
  by_cases small : count.sshiftRight 6 < BitVec.ofNat 32 4
  · simp only [Bool.false_eq_true, ite_false, ite_eq_left small]
    exact ready _ reference middle small (Or.inl rfl) slot loaded preserved middleCall middleAuthority next
  · simp only [Bool.false_eq_true, ite_false, ite_eq_right small]
    apply shift_count_guard true middle frame args (count.sshiftRight 6) reference slot loaded post
    by_cases nonnegative : 0 ≤ (count.sshiftRight 6).toInt
    · simp only [ite_true, ite_eq_left nonnegative]
      exact zero middle small (Or.inl nonnegative) preserved middleCall middleAuthority next
    · simp only [ite_true, ite_eq_right nonnegative]
      apply shift_negative_count_guard middle frame args count argument post
      by_cases multiple : count &&& (63 : BitVec 32) = 0
      · simp only [multiple, beq_self_eq_true, Bool.not_true, Bool.false_eq_true]
        exact zero middle small (Or.inr multiple) preserved middleCall middleAuthority next
      · simp only [bne_iff_ne, ite_eq_left multiple]
        apply shift_negative_count_reset boundary entered middle inputs outputs frame args
          middleCall enteredWF homes middleAuthority post
        intro resetHome after resetSlot resetRead retained afterCall afterAuthority resetWrite
        exact ready 0 resetHome after (by decide) (Or.inr ⟨rfl, by omega, multiple⟩)
          resetSlot resetRead (preserved.trans retained) afterCall afterAuthority
          (Nat.le_trans next (write_extends_allocations _ _ _ _ _ resetWrite).next)

#print axioms shift_count_dispatch
end UInt256Proof.Shift.Safety
