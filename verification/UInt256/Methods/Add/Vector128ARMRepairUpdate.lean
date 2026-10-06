import UInt256.Methods.Add.Vector128ARMRepairCarry

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose the carry-mask and high-result overwrites, retaining every other
    private vector and the exact initialized values of both updated homes. -/
theorem vector128_arm_update_pair (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (carry : BitVec 128) (carryHome : Reference)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (propagation : BitVec 128) (propagationHome : Reference)
    (propagationSlot : frame.locals[13]? = some (.bytes .vector128 propagationHome))
    (propagationRead : read current propagationHome 16 1 = .ok (numberBytes propagation.toNat 16))
    (full : BitVec 128) (fullHome : Reference)
    (fullSlot : frame.locals[21]? = some (.bytes .vector128 fullHome))
    (fullRead : read current fullHome 16 1 = .ok (numberBytes full.toNat 16))
    (repair : BitVec 128) (repairHome : Reference)
    (repairSlot : frame.locals[23]? = some (.bytes .vector128 repairHome))
    (repairRead : read current repairHome 16 1 = .ok (numberBytes repair.toNat 16))
    (high : BitVec 128) (highHome : Reference)
    (highSlot : slots[10]? = some (.bytes .vector128 highHome))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ updatedCarry updatedHigh after,
      slots[6]? = some (.bytes .vector128 updatedCarry) →
      slots[10]? = some (.bytes .vector128 updatedHigh) →
      read after updatedCarry 16 1 = .ok (numberBytes (repaired128Carry carry propagation full repair).toNat 16) →
      read after updatedHigh 16 1 = .ok (numberBytes (corrected128 high repair).toNat 16) →
      (∀ i, i ≠ 6 → i ≠ 10 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 149 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 137 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_arm_repair_carry enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority carry carryHome carrySlot carryRead
    propagation propagationHome propagationSlot propagationRead full fullHome fullSlot fullRead
    repair repairHome repairSlot repairRead post
  intro updatedCarry middle updatedCarrySlot updatedCarryRead preserved middleCall middleAuthority firstWrite
  have carryTail : slots[6]? = some (.bytes .vector128 updatedCarry) := by simpa [layout] using updatedCarrySlot
  have repairTail : slots[22]? = some (.bytes .vector128 repairHome) := by simpa [layout] using repairSlot
  have savedHigh := vector128_other_read entered current middle boundary slots homes 10 6 (by decide)
    highHome updatedCarry highSlot carryTail _ _ firstWrite highRead
  have savedRepair := vector128_other_read entered current middle boundary slots homes 22 6 (by decide)
    repairHome updatedCarry repairTail carryTail _ _ firstWrite repairRead
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  apply vector128_arm_repair_value enabled boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true high repair highHome repairHome actualHigh repairSlot savedHigh savedRepair post
  intro updatedHigh after updatedHighSlot updatedHighRead kept afterCall afterAuthority secondWrite
  have highTail : slots[10]? = some (.bytes .vector128 updatedHigh) := by simpa [layout] using updatedHighSlot
  have savedCarry := vector128_other_read entered middle after boundary slots homes 6 10 (by decide)
    updatedCarry updatedHigh carryTail highTail _ _ secondWrite updatedCarryRead
  have others : ∀ i, i ≠ 6 → i ≠ 10 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i notCarry notHigh reference bytes slot loaded
    exact vector128_other_read entered middle after boundary slots homes i 10 notHigh
      reference updatedHigh slot highTail _ _ secondWrite
      (vector128_other_read entered current middle boundary slots homes i 6 notCarry
        reference updatedCarry slot carryTail _ _ firstWrite loaded)
  exact continuation updatedCarry updatedHigh after carryTail highTail savedCarry updatedHighRead others
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_arm_update_pair
end UInt256Proof.Add.Safety
