import UInt256.Methods.Shift.SafetyCountStores

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Both private count stores retain the previously selected whole-limb count. -/
theorem shift_counts (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (count whole : BitVec 32) (wholeHome : Reference)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (wholeSlot : frame.locals[0]? = some (.bytes .word32 wholeHome))
    (wholeRead : read current wholeHome 4 1 = .ok (numberBytes whole.toNat 4))
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ maskHome complementHome after,
      frame.locals[1]? = some (.bytes .word32 maskHome) →
      frame.locals[2]? = some (.bytes .word32 complementHome) →
      read after wholeHome 4 1 = .ok (numberBytes whole.toNat 4) →
      read after maskHome 4 1 = .ok (numberBytes (count &&& (63 : BitVec 32)).toNat 4) →
      read after complementHome 4 1 =
        .ok (numberBytes ((63 : BitVec 32) - (count &&& 63)).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex shiftCountEnd args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 19) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply shift_mask_count boundary entered current inputs outputs frame args count argument
    call enteredWF homes authority post
  intro maskHome middle maskSlot maskRead preserved middleCall middleAuthority firstWrite
  have keptWhole := write_preserves_disjoint_read firstWrite wholeRead
    (Or.inl (Nat.ne_of_lt (homes.ordered 0 1 .word32 .word32 wholeHome maskHome (by decide) wholeSlot maskSlot)))
  apply shift_complement_count boundary entered middle inputs outputs frame args (count &&& 63)
    maskHome maskSlot maskRead middleCall enteredWF homes middleAuthority post
  intro complementHome after complementSlot complementRead retained afterCall afterAuthority secondWrite
  have wholeAfter := write_preserves_disjoint_read secondWrite keptWhole
    (Or.inl (Nat.ne_of_lt (homes.ordered 0 2 .word32 .word32 wholeHome complementHome (by decide) wholeSlot complementSlot)))
  have maskAfter := write_preserves_disjoint_read secondWrite maskRead
    (Or.inl (Nat.ne_of_lt (homes.ordered 1 2 .word32 .word32 maskHome complementHome (by decide) maskSlot complementSlot)))
  exact continuation maskHome complementHome after maskSlot complementSlot wholeAfter maskAfter complementRead
    (preserved.trans retained) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms shift_counts
end UInt256Proof.Shift.Safety
