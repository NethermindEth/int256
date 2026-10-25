import UInt256.Methods.Shift.ScalarCount

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
include bodyFound

theorem shift_mask_count (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[1]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes (count &&& (63 : BitVec 32)).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (count &&& (63 : BitVec 32)).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index (23) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (19) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (scalarBody profile direction storage) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 1 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 (count &&& (63 : BitVec 32))) (count &&& (63 : BitVec 32)).toNat rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  cil_contract_steps 3 [argument]
  exact run_next_exists post found rfl (stored _ _ _) done

theorem shift_complement_count (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (countHome : Reference)
    (countSlot : frame.locals[1]? = some (.bytes .word32 countHome))
    (countRead : read current countHome 4 1 = .ok (numberBytes count.toNat 4))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[2]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes ((63 : BitVec 32) - count).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes ((63 : BitVec 32) - count).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index 27 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (23) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (scalarBody profile direction storage) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 2 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 ((63 : BitVec 32) - count)) ((63 : BitVec 32) - count).toNat rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  have load := load_numeric_local .word32 (.i32 count) count.toNat rfl countRead
  cil_contract_steps 3 [countSlot, load]
  exact run_next_exists post found rfl (stored _ _ _) done

#print axioms shift_mask_count
#print axioms shift_complement_count
end UInt256Proof.Shift.Safety
