import CIL.Safety.WordSnapshotPreservation
import UInt256.Safety.PrivateWords

namespace UInt256Model.Safety
open CIL.Safety

/-- A checked vector-home write returns its initialized readback and preserves
    the original caller bytes and all remembered private words. -/
theorem PrivateWords.store_vector {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {body : CIL.Method} {frame : Frame} {known : Nat → Option (BitVec 64)}
    {kinds : List CIL.LocalKind}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (index : Nat) (specified : kinds[index]? = some .vector256) (value : BitVec 256)
    (pc : Nat) (args rest : List Value) :
    ∃ after reference,
      frame.locals[index]? = some (.bytes .vector256 reference) ∧
      step body (.setLocal index) pc args frame (.scalar (.v256 value) :: rest) current =
        .ok (.next (pc + 1) rest frame after) ∧
      PrivateWords program original entered after inputs outputs frame known ∧
      read after reference 32 1 = .ok (numberBytes value.toNat 32) ∧
      write current reference (numberBytes value.toNat 32) 1 = .ok after := by
  obtain ⟨reference, slot, bound, ready⟩ := homes.home_at index .vector256 specified
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have writable := state.authority.access ready (enteredWF.1 _ _ requirements.present).1
  obtain ⟨after, stepped, written, readback⟩ := step_store_numeric_local
    (body := body) (pc := pc) (args := args) (rest := rest) .vector256 (.v256 value) value.toNat rfl slot writable
  have preserved := write_preserves_memory_below _ _ _ _ _ _ bound written
  have authority := write_preserves_access_below written current.nextIdentity
  refine ⟨after, reference, slot, stepped, ?_, readback, written⟩
  refine ⟨state.call.after_write written, state.enteredBound,
    Nat.le_trans state.next (write_extends_allocations _ _ _ _ _ written).next,
    state.authority.trans (authority.weaken state.next),
    state.snapshots.after_other_kind_write homes index .vector256 reference (by decide) slot written, ?_⟩
  intro id old offset
  exact (preserved.cells id old offset).trans (state.caller id old offset)

#print axioms PrivateWords.store_vector
end UInt256Model.Safety
