import UInt256.Methods.Add.Vector128Propagation

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose both propagation masks while retaining every earlier vector home
    and all older caller storage, including ARM's early output readbacks. -/
theorem vector128_propagation_pair (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high incomingLow incomingHigh : BitVec 128)
    (lowHome highHome lowIncoming highIncoming : Reference)
    (lowSlot : slots[9]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[10]? = some (.bytes .vector128 highHome))
    (lowIncomingSlot : slots[7]? = some (.bytes .vector128 lowIncoming))
    (highIncomingSlot : slots[8]? = some (.bytes .vector128 highIncoming))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowIncomingRead : read current lowIncoming 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (highIncomingRead : read current highIncoming 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowMask highMask after,
      slots[11]? = some (.bytes .vector128 lowMask) →
      slots[12]? = some (.bytes .vector128 highMask) →
      read after lowMask 16 1 = .ok (numberBytes (propagating128 low incomingLow).toNat 16) →
      read after highMask 16 1 = .ok (numberBytes (propagating128 high incomingHigh).toNat 16) →
      (∀ i, i < 11 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 94 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 82 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actualLow : frame.locals[10]? = some (.bytes .vector128 lowHome) := by simpa [layout] using lowSlot
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  have actualLowIncoming : frame.locals[8]? = some (.bytes .vector128 lowIncoming) := by simpa [layout] using lowIncomingSlot
  have actualHighIncoming : frame.locals[9]? = some (.bytes .vector128 highIncoming) := by simpa [layout] using highIncomingSlot
  apply vector128_propagation_checked boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low incomingLow lowHome lowIncoming actualLow actualLowIncoming lowRead lowIncomingRead post
  intro lowMask middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[11]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowLocal
  have savedHigh := vector128_prior_read entered current middle boundary slots homes 10 11 (by decide)
    highHome lowMask highSlot lowTail _ _ firstWrite highRead
  have savedIncoming := vector128_prior_read entered current middle boundary slots homes 8 11 (by decide)
    highIncoming lowMask highIncomingSlot lowTail _ _ firstWrite highIncomingRead
  apply vector128_propagation_checked boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true high incomingHigh highHome highIncoming actualHigh actualHighIncoming savedHigh savedIncoming post
  intro highMask after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[12]? = some (.bytes .vector128 highMask) := by simpa [layout] using highLocal
  have lower := vector128_prior_read entered middle after boundary slots homes 11 12 (by decide)
    lowMask highMask lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 11 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read entered middle after boundary slots homes i 12 (by omega)
      reference highMask slot highTail _ _ secondWrite
      (vector128_prior_read entered current middle boundary slots homes i 11 bound
        reference lowMask slot lowTail _ _ firstWrite loaded)
  exact continuation lowMask highMask after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_propagation_pair
end UInt256Proof.Add.Safety
