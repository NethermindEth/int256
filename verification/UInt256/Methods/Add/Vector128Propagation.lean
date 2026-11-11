import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.Vector128EarlyOutput

/-!
Vector128 addition's propagation masks: a carry propagates through a lane whose speculative
result is zero and whose incoming carry is set.
-/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def propagationCode : List CIL.Op := [
  .local 10, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 8, .intrinsic (.vector (.band 128)) 2, .setLocal 12,
  .local 11, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 9, .intrinsic (.vector (.band 128)) 2, .setLocal 13]

/-- Store both propagation masks from the saved results and incoming carries. -/
theorem vector128_propagation_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 82 propagationCode)
    (lowSpec : specs[11]? = some vector128ZeroSpec)
    (highSpec : specs[12]? = some vector128ZeroSpec)
    (boundary : Nat) (origin entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots) (value : Nat → BitVec 128)
    (lowMask : value 11 = propagating128 (value 9) (value 7))
    (highMask : value 12 = propagating128 (value 10) (value 8))
    (state : VectorState program boundary origin entered current inputs outputs slots value 11)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program boundary origin entered after inputs outputs slots value 13 →
      ∃ fuel result returned,
        run program fuel method 94 args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method 82 args frame [] current = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨middle, lowState, storeLow⟩ :=
    state.store body specs frame root layout enteredWF homes lowSpec _ lowMask
  obtain ⟨after, highState, storeHigh⟩ :=
    lowState.store body specs frame root layout enteredWF homes highSpec _ highMask
  have loadLow := state.snapshots.load frame root layout 9 (by decide) body
  have loadLowIncoming := state.snapshots.load frame root layout 7 (by decide) body
  have loadHigh := lowState.snapshots.load frame root layout 10 (by decide) body
  have loadHighIncoming := lowState.snapshots.load frame root layout 8 (by decide) body
  cil_contract_steps [found, code, loadLow, loadLowIncoming, loadHigh, loadHighIncoming,
    storeLow, storeHigh, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128,
    CIL.Vector.intrinsic_and128, propagating128] until continuation after highState

/-- The thirteen private vectors saved before the fast/repair decision. -/
def vector128BranchValue (memory : Memory) (left right : Reference) (i : Fin 13) : BitVec 128 :=
  if within : i.val < 11 then vector128SnapshotValue memory left right ⟨i.val, within⟩
  else if i.val = 11 then
    propagating128 (vector128SnapshotValue memory left right 9) (vector128SnapshotValue memory left right 7)
  else propagating128 (vector128SnapshotValue memory left right 10) (vector128SnapshotValue memory left right 8)

end UInt256Proof.Add.Safety
