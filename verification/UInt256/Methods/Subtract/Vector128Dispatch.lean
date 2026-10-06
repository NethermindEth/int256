import UInt256.Methods.Subtract.Vector128Decision

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128InitialPropagation (memory : Memory) (left right : Reference) : BitVec 128 :=
  let values := vector128IncomingValue (vector128InputValues memory left right)
  vector128Propagation (values 4) (values 5) (values 8) (values 9)

/-- The complete read-only prefix reaches the selected branch with all ten
    initialized snapshots and caller memory still equal to the initial state. -/
theorem vector128_dispatch (original entered : Memory)
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
        run Extracted.program fuel vector128Index
          (if vector128InitialPropagation original left right = BitVec.ofNat 128 0 then 119 else 77) args (vector128SavedFrame frame slots right) [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered = .ok (final, returned) ∧ post final returned := by
  apply vector128_incoming_entry original entered inputs outputs left right frame slots args call setup layout homes
    leftMember rightMember leftArg rightArg post
  intro current snapshots preserved currentCall authority next
  obtain ⟨low, lowSlot, lowRead⟩ := snapshots 4
  obtain ⟨high, highSlot, highRead⟩ := snapshots 5
  obtain ⟨incomingLow, incomingLowSlot, incomingLowRead⟩ := snapshots 8
  obtain ⟨incomingHigh, incomingHighSlot, incomingHighRead⟩ := snapshots 9
  apply vector128_decision current (vector128SavedFrame frame slots right) args _ _ _ _
    low high incomingLow incomingHigh lowSlot highSlot incomingLowSlot incomingHighSlot
    lowRead highRead incomingLowRead incomingHighRead post
  exact continuation current snapshots preserved currentCall authority next

#print axioms vector128_dispatch
end UInt256Proof.Subtract.Safety
