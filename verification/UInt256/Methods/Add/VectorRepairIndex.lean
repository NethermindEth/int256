import UInt256.Methods.Add.VectorRepairMasks
import UInt256.Methods.AddSubtract.CascadeIndexExecution

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Checked scalar index arithmetic, including both overwrites of slot seven.
    Its final mask proves the lookup index is below sixteen. -/
theorem repair_index_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (generatedHome equalHome : Reference) (generated equal : BitVec 32)
    (generatedSlot : frame.locals[0]? = some (.bytes .word32 generatedHome))
    (equalSlot : frame.locals[1]? = some (.bytes .word32 equalHome))
    (generatedRead : read current generatedHome 4 1 = .ok (numberBytes generated.toNat 4))
    (equalRead : read current equalHome 4 1 = .ok (numberBytes equal.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∀ sumHome indexHome after,
      frame.locals[0]? = some (.bytes .word32 sumHome) →
      frame.locals[1]? = some (.bytes .word32 indexHome) →
      read after sumHome 4 1 = .ok (numberBytes (equal + 2 * generated).toNat 4) →
      read after indexHome 4 1 = .ok (numberBytes (UInt256Proof.SIMD.cascadeIndex generated equal).toNat 4) →
      (UInt256Proof.SIMD.cascadeIndex generated equal).toNat < 16 →
      MemoryBelow sumHome.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel repairIndex 24 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel repairIndex 10 args frame [] current =
        .ok (result, returned) ∧ post result returned :=
  cascade_index_checked boundary entered current inputs outputs frame args currentCall enteredWF homes authority
    generatedHome equalHome generated equal generatedSlot equalSlot generatedRead equalRead post continuation

#print axioms repair_index_checked
end UInt256Proof.Add.Safety
