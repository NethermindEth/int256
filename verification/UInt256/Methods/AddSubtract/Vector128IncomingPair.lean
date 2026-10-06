import UInt256.Methods.AddSubtract.Vector128Incoming

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety CIL.Vector

/-- Both selected incoming-mask blocks preserve every earlier initialized
    vector home, including the initial operands, upper sum and generated masks. -/
theorem vector128_incoming_pair (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high : BitVec 128) (stack : List Value) (lowHome highHome : Reference)
    (lowSlot : slots[5 + incoming128Offset]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[6 + incoming128Offset]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowIncoming highIncoming after,
      slots[7 + incoming128Offset]? = some (.bytes .vector128 lowIncoming) →
      slots[8 + incoming128Offset]? = some (.bytes .vector128 highIncoming) →
      read after lowIncoming 16 1 = .ok (numberBytes (incoming128Low low).toNat 16) →
      read after highIncoming 16 1 = .ok (numberBytes (incoming128High low high).toNat 16) →
      (∀ i, i < 7 + incoming128Offset → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (62 + incoming128Offset) args frame stack after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (37 + incoming128Offset) args frame stack current =
        .ok (result, returned) ∧ post result returned := by
  have actualLow : frame.locals[6 + incoming128Offset]? = some (.bytes .vector128 lowHome) := by
    simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lowSlot
  have actualHigh : frame.locals[7 + incoming128Offset]? = some (.bytes .vector128 highHome) := by
    simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using highSlot
  apply vector128_incoming_dispatch current frame args stack post
  apply vector128_incoming_checked boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low high stack lowHome highHome actualLow actualHigh lowRead highRead post
  intro lowIncoming middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[7 + incoming128Offset]? = some (.bytes .vector128 lowIncoming) := by simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lowLocal
  have savedLow := vector128_prior_read entered current middle boundary slots homes (5 + incoming128Offset) (7 + incoming128Offset) (by omega)
    lowHome lowIncoming lowSlot lowTail _ _ firstWrite lowRead
  have savedHigh := vector128_prior_read entered current middle boundary slots homes (6 + incoming128Offset) (7 + incoming128Offset) (by omega)
    highHome lowIncoming highSlot lowTail _ _ firstWrite highRead
  apply vector128_incoming_checked boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true low high stack lowHome highHome actualLow actualHigh savedLow savedHigh post
  intro highIncoming after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[8 + incoming128Offset]? = some (.bytes .vector128 highIncoming) := by simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using highLocal
  have lower := vector128_prior_read entered middle after boundary slots homes (7 + incoming128Offset) (8 + incoming128Offset) (by omega)
    lowIncoming highIncoming lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 7 + incoming128Offset → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read entered middle after boundary slots homes i (8 + incoming128Offset) (by omega)
      reference highIncoming slot highTail _ _ secondWrite
      (vector128_prior_read entered current middle boundary slots homes i (7 + incoming128Offset) bound
        reference lowIncoming slot lowTail _ _ firstWrite loaded)
  apply vector128_incoming_join after frame args stack post
  exact continuation lowIncoming highIncoming after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_incoming_pair
end UInt256Proof.AddSubtract.Safety
