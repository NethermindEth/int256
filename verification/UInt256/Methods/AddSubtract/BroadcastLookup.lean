import CIL.Safety.Equations
import UInt256.Methods.AddSubtract.BroadcastTable
import UInt256.LookupTable
import UInt256.Arithmetic.Cascade
import CIL.Safety.StaticMemoryBelow
import CIL.Safety.StaticInitialization
import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.AccessSlices
import CIL.Safety.StepComposition
import CIL.Safety.ByteRoundTrip
import CIL.Safety.CallComposition
import CIL.Safety.ExecutionLifetime
import UInt256.Safety.VectorFrame
import CIL.Safety.BufferContents

namespace UInt256Proof.AddSubtract.Vector256
open CIL.Safety UInt256Proof.SIMD

/-- Every 32-byte row of the table is the cascade vector of its index. -/
theorem table_rows : ∀ index : Fin 16,
    (broadcastTable.drop (32 * index.val)).take 32 =
      numberBytes (cascadeVector (BitVec.ofNat 32 index.val)).toNat 32 := by
  decide

/-- Resolving the readonly table allocates nothing below the caller boundary and binds the extracted bytes. -/
theorem lookup_invoke (program : CIL.Program) (index : Nat) (profile : CIL.FeatureProfile)
    (found : program[index]? = some (lookupBody profile)) (memory : Memory) (wf : memory.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) memory) :
    ∃ after reference,
      invoke program 4 index [] memory = .ok (after, [.span (.address reference) 512]) ∧
      MemoryBelow memory.nextIdentity memory after ∧ after.WellFormed ∧
      StaticWorldValid (programStaticDescriptors program) after ∧
      read after reference 512 1 = .ok broadcastTable := by
  have bytes : broadcastDescriptor.bytes = broadcastTable := rfl
  have selected : broadcastDescriptor ∈ programStaticDescriptors program :=
    program_static_sites_valid program index _ found (0, broadcastDescriptor) (by simp [lookupBody])
  obtain ⟨after, reference, resolved, afterWorld, binding⟩ :=
    staticReference_valid_result broadcastDescriptor _ memory wf world selected
  have below := staticReference_preserves_memory_below _ _ _ _ resolved
  have afterWF := staticReference_preserves_wellFormed _ _ _ _ wf resolved
  obtain ⟨offset, allocation, present, live, kind, size, loaded⟩ := binding
  rw [bytes] at size loaded
  have length : broadcastTable.length = 512 := by decide +kernel
  rw [length] at size loaded
  refine ⟨after, reference, ?_, below, afterWF, afterWorld, loaded⟩
  have formed : form after reference = .ok reference := by
    have ready := read_access loaded
    exact access_reference_valid _ _ _ _ _ ready
  simp [invoke, found, lookupBody, enterFrame, makeSelectedLocals, makeLocals, makeArgumentHomes, makeParameterHomes,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError]
  repeat'
    first
    | apply Eq.trans
      · apply run_next found (by rfl)
        simp (config := { implicitDefEqProofs := false })
          [step, cil_guard, observerCount, lookupBody, staticInstruction, bytes, resolved, checkedValue, formValue,
            formed, checkedAt, liveAllocation, present, live, kind, size, offset, pureArity,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | simp [run, found, lookupBody, step, cil_guard, observerCount, leaveFrame, checkedValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A masked index selects one in-bounds 32-byte row, which decodes to its cascade vector. -/
theorem table_row (memory : Memory) (reference : Reference) (wf : memory.WellFormed)
    (loaded : read memory reference 512 1 = .ok broadcastTable) (index : BitVec 32) (small : index.toNat < 16) :
    add memory reference 32 (BitVec.ofInt 64 ((index.zeroExtend 64).toNat : Int)) =
        .ok { reference with offset := reference.offset + 32 * index.toNat } ∧
      loadValue memory (.address { reference with offset := reference.offset + 32 * index.toNat }) 32 =
        .ok (.v256 (cascadeVector index)) := by
  have ready := read_access loaded
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have offset : BitVec.ofInt 64 ((index.zeroExtend 64).toNat : Int) = BitVec.ofNat 64 index.toNat := by
    rw [BitVec.ofInt_natCast]
    congr 1
  refine ⟨?_, ?_⟩
  · rw [offset]
    exact requirements.add_slice wf 32 index.toNat 32 (by decide) (by omega)
  · have row := read_slice_bytes wf loaded (32 * index.toNat) 32 (by decide) (by omega)
    rw [table_rows ⟨index.toNat, small⟩] at row
    have same : BitVec.ofNat 32 index.toNat = index := by simp
    rw [same] at row
    simp only [loadValue, dereference, row, checkedAt, ordinaryAccessAlignment, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp [element_value (width := 32) (cascadeVector index)]

#print axioms table_row
#print axioms table_rows
#print axioms lookup_invoke

open UInt256Model.Safety in
/-- Calling the table getter keeps every remembered frame fact and yields a readable table span. -/
theorem run_lookup {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {frame : Frame}
    {known : Nat → Option CIL.Value} {stored : Option (BitVec 256)}
    {body : CIL.Method} {method pc lookup : Nat} {args stack : List Value} {profile : CIL.FeatureProfile}
    (post : Memory → List Value → Prop)
    (state : VectorFrame program original entered current inputs output frame known stored)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.call lookup 0))
    (lookupFound : program[lookup]? = some (lookupBody profile))
    (continuation : ∀ after reference,
      VectorFrame program original entered after inputs output frame known stored →
      read after reference 512 1 = .ok broadcastTable → form after reference = .ok reference →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (.span (.address reference) 512 :: stack) after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack current = .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, reference, invoked, below, wf, world, loaded⟩ :=
    lookup_invoke program lookup profile lookupFound current state.call.1.1 state.call.2
  have grown := (invoke_preserves_caller_allocations program 4 lookup [] _ current after invoked).next
  have next := state.after_call below wf world grown
  have stepped : step body (.call lookup 0) pc args frame stack current =
      .ok (.call lookup [] stack current) := by
    simp [step, cil_guard, observerCount, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, result, returned, finished, satisfied⟩ :=
    continuation after reference next loaded (read_reference_valid _ _ _ _ _ loaded)
  obtain ⟨total, ran⟩ := run_call_exists found fetched stepped ⟨4, invoked⟩ ⟨fuel, finished⟩
  exact ⟨total, result, returned, ran, satisfied⟩

#print axioms run_lookup
end UInt256Proof.AddSubtract.Vector256
