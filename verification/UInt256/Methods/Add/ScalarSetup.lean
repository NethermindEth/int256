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

#print axioms scalar_local_metadata
#print axioms scalar_frame_setup

/-- Any word selected by the extracted initializer metadata can be updated by
    the actual local-store instruction, retaining its frame identity and exact
    byte readback. Null reference-root slots cannot satisfy `specified`. -/
theorem scalar_store_local {memory : Memory} {lower : Nat} {frame : Frame}
    (homes : WordHomes memory lower scalarLocalSpecs frame.locals)
    (index : Nat) (initial value : BitVec 64)
    (specified : scalarLocalSpecs[index]? = some (some initial))
    (pc : Nat) (args rest : List Value) :
    ∃ reference result,
      frame.locals[index]? = some (.bytes .word64 reference) ∧
      lower ≤ reference.allocation ∧
      step Extracted.addScalarBody (.setLocal index) pc args frame
        (.scalar (.i64 value) :: rest) memory = .ok (.next (pc + 1) rest frame result) ∧
      write memory reference (numberBytes value.toNat 8) 1 = .ok result ∧
      read result reference 8 1 = .ok (numberBytes value.toNat 8) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.word_at index initial specified
  obtain ⟨result, stepped, written, loaded⟩ := step_store_word64_same_frame
    (body := Extracted.addScalarBody) (pc := pc) (args := args) (rest := rest) value slot writable
  exact ⟨reference, result, slot, bound, stepped, written, loaded⟩

#print axioms scalar_store_local

end UInt256Proof.Safety
