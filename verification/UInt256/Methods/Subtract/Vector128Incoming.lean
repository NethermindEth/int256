import UInt256.Methods.Subtract.Vector128Prepared
import UInt256.Methods.AddSubtract.Vector128IncomingPair

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

@[simp] theorem incoming128Offset_subtract : incoming128Offset = 1 := by rfl

def vector128IncomingValue (values : Fin 4 → BitVec 128) (i : Fin 10) : BitVec 128 :=
  if h : i.val < 8 then vector128PreparedValue values ⟨i.val, h⟩
  else if i.val = 8 then incoming128Low (vector128PreparedValue values 6)
  else incoming128High (vector128PreparedValue values 6) (vector128PreparedValue values 7)

/-- The operand, difference and borrow snapshots remain initialized through both
    incoming-mask stores; their values refer to the initial caller operands. -/
theorem vector128_incoming_entry (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vector128Body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 10, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes
          (vector128IncomingValue (vector128InputValues original left right) i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 63 args (vector128SavedFrame frame slots right) [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered = .ok (final, returned) ∧ post final returned := by
  apply vector128_prepared_entry original entered inputs outputs left right frame slots args call setup layout homes
    leftMember rightMember leftArg rightArg post
  intro current snapshots preserved currentCall authority next
  obtain ⟨low, lowSlot, lowRead⟩ := snapshots 6
  obtain ⟨high, highSlot, highRead⟩ := snapshots 7
  apply vector128_incoming_pair original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    (vector128PreparedValue (vector128InputValues original left right) 6)
    (vector128PreparedValue (vector128InputValues original left right) 7) [] low high lowSlot highSlot lowRead highRead post
  intro lowIncoming highIncoming after lowIncomingSlot highIncomingSlot lowIncomingRead highIncomingRead
    kept retained afterCall afterAuthority advanced
  have allSnapshots : ∀ i : Fin 10, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes
        (vector128IncomingValue (vector128InputValues original left right) i).toNat 16) := by
    intro i
    by_cases earlier : i.val < 8
    · obtain ⟨reference, slot, loaded⟩ := snapshots ⟨i.val, earlier⟩
      refine ⟨reference, slot, ?_⟩
      simp only [vector128IncomingValue, dite_eq_left earlier]
      exact kept i.val earlier reference _ slot loaded
    · have cases : i = 8 ∨ i = 9 := by omega
      rcases cases with rfl | rfl
      · exact ⟨lowIncoming, lowIncomingSlot, lowIncomingRead⟩
      · exact ⟨highIncoming, highIncomingSlot, highIncomingRead⟩
  exact continuation after allSnapshots (preserved.trans retained) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms vector128_incoming_entry
end UInt256Proof.Subtract.Safety
