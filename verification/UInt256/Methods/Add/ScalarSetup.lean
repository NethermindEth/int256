import UInt256.Methods.Add.Bindings
import CIL.Safety.WordFrameSetup

namespace UInt256Proof.Safety

open CIL.Safety

/-- Read the initializer recipe from extraction; the checked metadata equations
    below reject any initializer or kind outside the supported word/root recipe. -/
def scalarLocalSpecs : List (Option (BitVec 64)) :=
  Extracted.addScalarBody.locals.map fun value => match value with
    | .i64 word => some word
    | _ => none

theorem scalar_local_metadata :
    Extracted.addScalarBody.localKinds = wordKinds scalarLocalSpecs ∧
    Extracted.addScalarBody.locals = wordInitializers scalarLocalSpecs := by
  simp [scalarLocalSpecs, wordKinds, wordInitializers, cil_code]

/-- Actual setup provides indexed readable/writable word homes, distinct fresh
    identities, and unchanged older caller storage. No body-success assumption. -/
theorem scalar_frame_setup (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame Extracted.addScalarBody args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity scalarLocalSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  word_frame_setup Extracted.addScalarBody scalarLocalSpecs scalar_local_metadata.1
    scalar_local_metadata.2 (by simp only [cil_code]) (by simp only [cil_code]) (by rfl) memory args wellFormed

end UInt256Proof.Safety
