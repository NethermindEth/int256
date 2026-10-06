import UInt256.Methods.Add.Vector128ARMRepairExtra

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Both extra-propagation stores, preserving all earlier private snapshots. -/
theorem vector128_arm_extra_pair (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (result propagation : BitVec 128) (resultHome propagationHome : Reference)
    (resultSlot : slots[10]? = some (.bytes .vector128 resultHome))
    (propagationSlot : slots[19]? = some (.bytes .vector128 propagationHome))
    (resultRead : read current resultHome 16 1 = .ok (numberBytes result.toNat 16))
    (propagationRead : read current propagationHome 16 1 = .ok (numberBytes propagation.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ fullHome extraHome after,
      slots[20]? = some (.bytes .vector128 fullHome) →
      slots[21]? = some (.bytes .vector128 extraHome) →
      read after fullHome 16 1 = .ok (numberBytes (full128 result).toNat 16) →
      read after extraHome 16 1 = .ok (numberBytes (incoming128Low (full128 result &&& propagation)).toNat 16) →
      (∀ i, i < 20 → ∀ reference bytes, slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 133 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 122 args frame [] current = .ok (final, returned) ∧ post final returned := by
  have actualResult : frame.locals[11]? = some (.bytes .vector128 resultHome) := by simpa [layout] using resultSlot
  have actualPropagation : frame.locals[20]? = some (.bytes .vector128 propagationHome) := by simpa [layout] using propagationSlot
  apply vector128_arm_full_mask enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority result resultHome actualResult resultRead post
  intro fullHome middle fullSlot fullRead preserved middleCall middleAuthority firstWrite
  have fullTail : slots[20]? = some (.bytes .vector128 fullHome) := by simpa [layout] using fullSlot
  have savedPropagation := vector128_prior_read entered current middle boundary slots homes 19 20 (by decide)
    propagationHome fullHome propagationSlot fullTail _ _ firstWrite propagationRead
  apply vector128_arm_extra_mask enabled boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority (full128 result) fullHome fullSlot fullRead
    propagation propagationHome actualPropagation savedPropagation post
  intro extraHome after extraSlot extraRead kept afterCall afterAuthority secondWrite
  have extraTail : slots[21]? = some (.bytes .vector128 extraHome) := by simpa [layout] using extraSlot
  have savedFull := vector128_prior_read entered middle after boundary slots homes 20 21 (by decide)
    fullHome extraHome fullTail extraTail _ _ secondWrite fullRead
  have earlier : ∀ i, i < 20 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read entered middle after boundary slots homes i 21 (by omega)
      reference extraHome slot extraTail _ _ secondWrite
      (vector128_prior_read entered current middle boundary slots homes i 20 bound
        reference fullHome slot fullTail _ _ firstWrite loaded)
  exact continuation fullHome extraHome after fullTail extraTail savedFull extraRead earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_arm_extra_pair
end UInt256Proof.Add.Safety
