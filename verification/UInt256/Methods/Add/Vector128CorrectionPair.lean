import UInt256.Methods.Add.Vector128Correction

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Both speculative result stores retain the earlier operand, sum and mask
    snapshots. Only fresh private homes change at this stage. -/
theorem vector128_correction_pair (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high incomingLow incomingHigh : BitVec 128) (sumHome lowHome highHome : Reference)
    (sumSlot : slots[4]? = some (.bytes .vector128 sumHome))
    (lowSlot : slots[7]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[8]? = some (.bytes .vector128 highHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowResult highResult after,
      slots[9]? = some (.bytes .vector128 lowResult) →
      slots[10]? = some (.bytes .vector128 highResult) →
      read after lowResult 16 1 = .ok (numberBytes (corrected128 low incomingLow).toNat 16) →
      read after highResult 16 1 = .ok (numberBytes (corrected128 high incomingHigh).toNat 16) →
      (∀ i, i < 9 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 69 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 62 args frame [.scalar (.v128 low)] current =
        .ok (result, returned) ∧ post result returned := by
  have actualSum : frame.locals[5]? = some (.bytes .vector128 sumHome) := by
    simpa [layout] using sumSlot
  have actualLow : frame.locals[8]? = some (.bytes .vector128 lowHome) := by
    simpa [layout] using lowSlot
  have actualHigh : frame.locals[9]? = some (.bytes .vector128 highHome) := by
    simpa [layout] using highSlot
  apply vector128_correction_checked boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low high incomingLow sumHome lowHome actualSum actualLow sumRead lowRead post
  intro lowResult middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[9]? = some (.bytes .vector128 lowResult) := by simpa [layout] using lowLocal
  have savedSum := vector128_prior_read entered current middle boundary slots homes 4 9 (by decide)
    sumHome lowResult sumSlot lowTail _ _ firstWrite sumRead
  have savedHigh := vector128_prior_read entered current middle boundary slots homes 8 9 (by decide)
    highHome lowResult highSlot lowTail _ _ firstWrite highRead
  apply vector128_correction_checked boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true low high incomingHigh sumHome highHome actualSum actualHigh savedSum savedHigh post
  intro highResult after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[10]? = some (.bytes .vector128 highResult) := by simpa [layout] using highLocal
  have lower := vector128_prior_read entered middle after boundary slots homes 9 10 (by decide)
    lowResult highResult lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 9 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read entered middle after boundary slots homes i 10 (by omega)
      reference highResult slot highTail _ _ secondWrite
      (vector128_prior_read entered current middle boundary slots homes i 9 bound
        reference lowResult slot lowTail _ _ firstWrite loaded)
  exact continuation lowResult highResult after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_correction_pair
end UInt256Proof.Add.Safety
