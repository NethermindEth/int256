import CIL.Safety.SymbolicExecution
import CIL.Safety.ReturnArity
import CIL.Safety.LocalSnapshotSteps
import UInt256.Methods.Add.Vector128FastEntry

namespace UInt256Proof.Add.Safety
def armRepairCode : List CIL.Op := [
.arg 3 (some .unsigned8),
.brnonzero 117,
.local 14,
.branch 121,
.local 12,
.local 13,
.const32 1,
.intrinsic (.advSimd .extract64) 3,
.setLocal 20,
.local 11,
.intrinsic (.vector (.ones 128)) 0,
.intrinsic (.vector (.eq64 128)) 2,
.setLocal 21,
.intrinsic (.vector (.zero 128)) 0,
.local 21,
.local 20,
.intrinsic (.vector (.band 128)) 2,
.const32 1,
.intrinsic (.advSimd .extract64) 3,
.setLocal 22,
.local 20,
.local 22,
.intrinsic (.vector (.bor 128)) 2,
.setLocal 23,
.local 7,
.local 13,
.local 21,
.local 23,
.intrinsic (.vector (.band 128)) 2,
.intrinsic (.vector (.bor 128)) 2,
.intrinsic (.vector (.bor 128)) 2,
.setLocal 7,
.local 11,
.local 23,
.intrinsic (.vector (.sub64 128)) 2,
.setLocal 11,
.arg 2,
.memory .asRef,
.const32 1,
.memory (.add 16 true),
.local 11,
.memory .store128,
.local 7,
.const32 1,
.intrinsic (.vector (.extract64 128)) 2,
.const32 0,
.convI8,
.gtu,
.ret (some .unsigned8)
]
end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- Lanes of the high result that are all ones, where an incoming carry propagates further. -/
def full128 (result : BitVec 128) : BitVec 128 :=
  CIL.Vector.zip128 (fun x y => CIL.Vector.mask64 (x == y)) result (~~~0)

/-- Caller guarantees since `start` and the remembered private vectors behind the root slot. -/
structure Vector128State (program : CIL.Program) (boundary : Nat) (entered start current : Memory)
    (inputs outputs : List Reference) (slots : List LocalSlot)
    (values : List (Option CIL.Value)) : Prop where
  call : CallingConditions program current inputs outputs
  preserved : MemoryBelow boundary start current
  authority : AccessBelow entered.nextIdentity entered current
  advanced : start.nextIdentity ≤ current.nextIdentity
  snapshots : LocalSnapshots current slots (knownLocals values)

variable {program : CIL.Program} {boundary : Nat} {entered start current : Memory}
  {inputs outputs : List Reference} {slots : List LocalSlot} {values : List (Option CIL.Value)}

/-- Saved vector reads start a state that remembers them and nothing in the `spare` locals. -/
theorem Vector128State.initial {count : Nat} (saved : Fin count → BitVec 128) (spare : Nat)
    (call : CallingConditions program current inputs outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (reads : ∀ i : Fin count, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (saved i).toNat 16)) :
    Vector128State program boundary entered current current inputs outputs slots
      (List.ofFn (fun i => some (.v128 (saved i))) ++ List.replicate spare none) := by
  refine ⟨call, MemoryBelow.refl _ _, authority, Nat.le_refl _, ?_⟩
  intro index value specified
  by_cases bound : index < count
  · obtain ⟨reference, slot, loaded⟩ := reads ⟨index, bound⟩
    exact ⟨.vector128, reference, .v128 (saved ⟨index, bound⟩), _, slot, rfl,
      by simpa [knownLocals, List.getElem?_append, bound, localResult] using specified, loaded⟩
  · simp only [knownLocals, List.getElem?_append, List.length_ofFn, bound, ite_false,
      List.getElem?_replicate] at specified
    split at specified <;> cases specified

/-- The frame's locals remember the same vectors one slot after the root. -/
theorem Vector128State.locals
    (state : Vector128State program boundary entered start current inputs outputs slots values)
    {frame : Frame} {root : LocalSlot} (layout : frame.locals = root :: slots) :
    LocalSnapshots current frame.locals (knownLocals (none :: values)) := by
  rw [layout]
  exact state.snapshots.skip

/-- A remembered vector is an initialized sixteen-byte home holding exactly its bits. -/
theorem Vector128State.read
    (state : Vector128State program boundary entered start current inputs outputs slots values)
    {index : Nat} {value : BitVec 128} (known : knownLocals values index = some (.v128 value)) :
    ∃ reference, slots[index]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes value.toNat 16) := by
  obtain ⟨kind, home, stored, number, slot, fits, result, loaded⟩ := state.snapshots index _ known
  have vector : kind = .vector128 ∧ number = value.toNat := by
    cases kind <;> cases stored <;>
      simp_all [localResult, localNumber, CIL.Value.hasUnspecified] <;>
      (split at fits <;> simp_all)
  obtain ⟨rfl, rfl⟩ := vector
  exact ⟨home, slot, loaded⟩

/-- A checked private vector store remembers the value and keeps the caller guarantees. -/
theorem Vector128State.store
    (state : Vector128State program boundary entered start current inputs outputs slots values)
    (body : CIL.Method) {specs : List NumericLocalSpec} {frame : Frame} {root : LocalSlot}
    (layout : frame.locals = root :: slots) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots) (index : Nat) (behindRoot : 0 < index)
    (specified : specs[index - 1]? = some vector128ZeroSpec)
    (present : index - 1 < values.length) (value : BitVec 128) :
    ∃ after, Vector128State program boundary entered start after inputs outputs slots
        (values.set (index - 1) (some (.v128 value))) ∧
      ∀ pc args rest, step body (.setLocal index) pc args frame
        (.scalar (.v128 value) :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨home, after, slot, _, kept, call, authority, written, stepped⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root
      slots layout state.call enteredWF homes state.authority (index - 1) vector128ZeroSpec
      specified (.v128 value) value.toNat rfl
  rw [Nat.sub_add_cancel behindRoot] at slot stepped
  refine ⟨after, ⟨call, state.preserved.trans kept, authority,
    Nat.le_trans state.advanced (write_extends_allocations _ _ _ _ _ written).next, ?_⟩, stepped⟩
  rw [← rememberLocal_knownLocals present]
  refine state.snapshots.after_write homes.writable (index - 1) .vector128 home (.v128 value)
    value.toNat rfl ?_ written
  obtain ⟨tail, rfl⟩ : ∃ tail, index = tail + 1 := ⟨index - 1, by omega⟩
  simpa [layout, vector128ZeroSpec] using slot

end UInt256Proof.Add.Safety