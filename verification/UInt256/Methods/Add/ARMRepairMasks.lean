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

def armWordSpec : NumericLocalSpec := ⟨.word64, .i64 0, 0, rfl⟩

/-- Numeric locals of the ARM helper behind its root slot: fourteen saved vectors, five words
    and the four repair vectors. -/
def armSpecs : List NumericLocalSpec := List.replicate 14 vector128ZeroSpec ++
  List.replicate 5 armWordSpec ++ List.replicate 4 vector128ZeroSpec

theorem armSpecs_first : ∀ i : Fin 14, armSpecs[i.val]? = some vector128ZeroSpec := by
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> rfl

/-- What a frame's locals remember when the first `count` vectors behind its root slot hold
    `saved`. -/
def savedVectors {count : Nat} (saved : Fin count → BitVec 128) : Nat → Option CIL.Value :=
  fun index => if ready : 1 ≤ index ∧ index - 1 < count then
    some (.v128 (saved ⟨index - 1, ready.2⟩)) else none

/-- Saved vector reads behind the root slot are snapshots of the frame's locals. -/
theorem savedVectors_snapshots {count : Nat} {saved : Fin count → BitVec 128}
    {current : Memory} {frame : Frame} {root : LocalSlot} {slots : List LocalSlot}
    (layout : frame.locals = root :: slots)
    (reads : ∀ i : Fin count, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (saved i).toNat 16)) :
    LocalSnapshots current frame.locals (savedVectors saved) := by
  intro index value specified
  unfold savedVectors at specified
  split at specified
  next ready =>
    obtain ⟨reference, slot, loaded⟩ := reads ⟨index - 1, ready.2⟩
    obtain ⟨inner, rfl⟩ : ∃ inner, index = inner + 1 := ⟨index - 1, by omega⟩
    cases specified
    exact ⟨.vector128, reference, .v128 _, _, by simpa [layout] using slot, rfl, rfl, loaded⟩
  next => cases specified

end UInt256Proof.Add.Safety