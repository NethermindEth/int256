import UInt256.Methods.Add.Vector128ARMRepairArithmetic

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def repair128Mask (high lowPropagation highPropagation : BitVec 128) : BitVec 128 :=
  incoming128High lowPropagation highPropagation |||
    incoming128Low (full128 high &&& incoming128High lowPropagation highPropagation)

/-- All repair-mask preparation, retaining the fourteen original snapshots. -/
theorem vector128_arm_prepare (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (argument : args[3]? = some (.scalar (.i32 flag)))
    (values : Fin 14 → BitVec 128)
    (condition : values 13 = selectedPropagation128 flag (values 11) (values 12))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ fullHome repairHome after,
      slots[20]? = some (.bytes .vector128 fullHome) →
      slots[22]? = some (.bytes .vector128 repairHome) →
      read after fullHome 16 1 = .ok (numberBytes (full128 (values 10)).toNat 16) →
      read after repairHome 16 1 = .ok (numberBytes (repair128Mask (values 10) (values 11) (values 12)).toNat 16) →
      (∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 137 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 113 args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 11
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 12
  obtain ⟨conditionHome, conditionSlot, conditionRead⟩ := snapshots 13
  obtain ⟨resultHome, resultSlot, resultRead⟩ := snapshots 10
  change slots[11]? = _ at lowSlot
  change slots[12]? = _ at highSlot
  change slots[13]? = _ at conditionSlot
  change slots[10]? = _ at resultSlot
  have actualLow : frame.locals[12]? = some (.bytes .vector128 lowHome) := by simpa [layout] using lowSlot
  have actualHigh : frame.locals[13]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  have actualCondition : frame.locals[14]? = some (.bytes .vector128 conditionHome) := by simpa [layout] using conditionSlot
  rw [condition] at conditionRead
  apply vector128_arm_repair_mask enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority flag argument (values 11) (values 12) lowHome highHome
    actualLow actualHigh lowRead highRead conditionHome actualCondition conditionRead post
  intro propagationHome first propagationSlot propagationRead firstPreserved firstCall firstAuthority firstWrite
  have propagationTail : slots[19]? = some (.bytes .vector128 propagationHome) := by simpa [layout] using propagationSlot
  have savedResult := vector128_prior_read entered current first boundary slots homes 10 19 (by decide)
    resultHome propagationHome resultSlot propagationTail _ _ firstWrite resultRead
  have firstSnapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read first reference 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, vector128_prior_read entered current first boundary slots homes i.val 19 (by omega)
      reference propagationHome slot propagationTail _ _ firstWrite loaded⟩
  apply vector128_arm_extra_pair enabled boundary entered first inputs outputs frame root slots layout args
    firstCall enteredWF homes firstAuthority (values 10) (incoming128High (values 11) (values 12))
    resultHome propagationHome resultSlot propagationTail savedResult propagationRead post
  intro fullHome extraHome second fullSlot extraSlot fullRead extraRead kept secondPreserved secondCall secondAuthority secondNext
  have savedPropagation := kept 19 (by decide) propagationHome _ propagationTail propagationRead
  have actualExtra : frame.locals[22]? = some (.bytes .vector128 extraHome) := by simpa [layout] using extraSlot
  apply vector128_arm_repair_value enabled boundary entered second inputs outputs frame root slots layout args
    secondCall enteredWF homes secondAuthority false (incoming128High (values 11) (values 12))
    (incoming128Low (full128 (values 10) &&& incoming128High (values 11) (values 12)))
    propagationHome extraHome propagationSlot actualExtra savedPropagation extraRead post
  intro repairHome after repairSlot repairRead thirdPreserved afterCall afterAuthority thirdWrite
  have repairTail : slots[22]? = some (.bytes .vector128 repairHome) := by simpa [layout] using repairSlot
  have savedFull := vector128_prior_read entered second after boundary slots homes 20 22 (by decide)
    fullHome repairHome fullSlot repairTail _ _ thirdWrite fullRead
  have finalSnapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := firstSnapshots i
    exact ⟨reference, slot, vector128_prior_read entered second after boundary slots homes i.val 22 (by omega)
      reference repairHome slot repairTail _ _ thirdWrite (kept i.val (by omega) reference _ slot loaded)⟩
  exact continuation fullHome repairHome after fullSlot repairTail savedFull repairRead finalSnapshots
    ((firstPreserved.trans secondPreserved).trans thirdPreserved) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (Nat.le_trans secondNext (write_extends_allocations _ _ _ _ _ thirdWrite).next))

#print axioms vector128_arm_prepare
end UInt256Proof.Add.Safety
