import Extracted
import UInt256.LookupTable

set_option maxRecDepth 8192

namespace UInt256Proof.SIMD

if_extracted Extracted.broadcastLookupData {
theorem extracted_lookup_valid : LookupValid Extracted.broadcastLookupData := by
  unfold LookupValid
  simp only [readStaticBytes_sequential]
  -- Check the table once in the kernel, avoiding a second reduction in elaboration.
  decide +kernel
}

if_extracted Extracted.broadcastLookupIndex {
theorem execute_lookup (m : CIL.Memory) (frame fuel : Nat) :
    CIL.run Extracted.program
      (fuel + CIL.executionBound Extracted.program Extracted.broadcastLookupIndex)
      Extracted.broadcastLookupIndex 0 [] frame [] m =
    some (m, [.span (.static Extracted.broadcastLookupData 0) 512]) := by
  cil_steps CIL.evalMemory, Extracted.broadcastLookupData

theorem execute_lookup_at (m : CIL.Memory) (frame fuel : Nat)
    (hf : CIL.executionBound Extracted.program Extracted.broadcastLookupIndex ≤ fuel) :
    CIL.run Extracted.program fuel Extracted.broadcastLookupIndex 0 [] frame [] m =
    some (m, [.span (.static Extracted.broadcastLookupData 0) 512]) := by
  have he := execute_lookup m frame 0
  simp only [Nat.zero_add] at he
  exact CIL.run_of_le _ _ _ _ _ _ _ _ _ _ hf he
}

end UInt256Proof.SIMD
