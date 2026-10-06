import CIL.Safety.HomeProgress
import CIL.Safety.FrameMemoryBelow
import CIL.Safety.WriteEffects

namespace CIL.Safety

/-- Allocate and initialize a private 256-bit home using the checked memory operations. -/
theorem allocate_initialized256 (memory : Memory) (activation : Nat) (bits : BitVec 256)
    (wellFormed : memory.WellFormed) :
    ∃ reference allocated result,
      allocateHome memory activation 32 = .ok (reference, allocated) ∧
      storeValue allocated (.address reference) (.v256 bits) = .ok result ∧
      storeLocal allocated (.bytes .vector256 reference) (.scalar (.v256 bits)) =
        .ok (.bytes .vector256 reference, result) ∧
      read result reference 32 1 = .ok (numberBytes bits.toNat 32) ∧
      access result reference 32 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨reference, allocated, home⟩ :=
    allocateHome_succeeds memory activation 32 wellFormed (by decide)
  have ready := allocateHome_write_access _ _ _ _ _ home
  have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨result, written⟩ := write_succeeds (bytes := numberBytes bits.toNat 32)
    (by simpa only [length] using ready.access)
  have readback := write_readback _ _ _ _ _ written
  rw [length] at readback
  have stored : storeLocal allocated (.bytes .vector256 reference) (.scalar (.v256 bits)) =
      .ok (.bytes .vector256 reference, result) := by
    simp [storeLocal, localNumber, localWidth, written, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have created : makeLocal activation .vector256 (.v256 bits) memory =
      .ok (.bytes .vector256 reference, [reference.allocation], result) := by
    simp [makeLocal, localWidth, home, stored, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨reference, allocated, result, home, ?_, stored, readback, ?_,
    makeLocal_preserves_caller_memory _ _ _ _ _ _ _ created⟩
  · simp [storeValue, referenceAt, written, checkedAt,
      Except.mapError, Bind.bind, Except.bind]
  · simpa only [length] using (ready.after_write written).access

/-- The actual aggregate-argument setup initializes a private copy before its
    address is exposed to the method body. -/
theorem make_argument_home256 (memory : Memory) (activation index : Nat)
    (args : List Value) (bits : BitVec 256)
    (wellFormed : memory.WellFormed)
    (argument : args[index]? = some (.scalar (.v256 bits))) :
    ∃ reference result,
      makeArgumentHomes activation [index] args memory =
        .ok ([(index, .bytes .vector256 reference)], [reference.allocation], result) ∧
      read result reference 32 1 = .ok (numberBytes bits.toNat 32) ∧
      access result reference 32 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨reference, allocated, result, home, _, stored, readback, writable, preserved⟩ :=
    allocate_initialized256 memory activation bits wellFormed
  have made : makeArgumentHomes activation [index] args memory =
      .ok ([(index, .bytes .vector256 reference)], [reference.allocation], result) := by
    simp [makeArgumentHomes, argument, localWidth, home, stored,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨reference, result, made, readback, writable, preserved⟩

#print axioms allocate_initialized256
#print axioms make_argument_home256

end CIL.Safety
