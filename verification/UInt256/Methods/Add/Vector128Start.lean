import CIL.Safety.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.AddSubtract.Vector128Inputs

/-!
Vector128 addition from its saved operand halves to its carry masks: add both lanes and compare
each lane sum with its left operand.
-/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128AddPrefix : List CIL.Op := [
  .arg 0, .memory .asRef, .memory .asRef, .arg 1, .memory .asRef, .memory .asRef, .setLocal 0,
  .dup, .memory .load128, .setLocal 1,
  .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 2,
  .local 0, .memory .load128, .setLocal 3,
  .local 0, .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 4,
  .local 1, .local 3, .intrinsic (.vector (.add64 128)) 2,
  .local 2, .local 4, .intrinsic (.vector (.add64 128)) 2, .setLocal 5,
  .dup, .local 1, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 6,
  .local 5, .local 2, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 7]

/-- Store the upper lane sum and both carry masks, keeping the lower sum on the stack. -/
theorem vector128_sum_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 0 vector128AddPrefix)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (boundary : Nat) (origin entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots) (value : Nat → BitVec 128)
    (sum : value 4 = halfSum (value 1) (value 3))
    (lowMask : value 5 = halfCarry (halfSum (value 0) (value 2)) (value 0))
    (highMask : value 6 = halfCarry (value 4) (value 1))
    (state : VectorState program boundary origin entered current inputs outputs slots value 4)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program boundary origin entered after inputs outputs slots value 7 →
      ∃ fuel result returned,
        run program fuel method 37 args frame [.scalar (.v128 (halfSum (value 0) (value 2)))]
          after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨summed, sumState, storeSum⟩ :=
    state.store body specs frame root layout enteredWF homes (firstSeven 4) _ sum
  obtain ⟨masked, lowState, storeLow⟩ :=
    sumState.store body specs frame root layout enteredWF homes (firstSeven 5) _ lowMask
  obtain ⟨after, highState, storeHigh⟩ :=
    lowState.store body specs frame root layout enteredWF homes (firstSeven 6) _ highMask
  have loadLeftLow := state.snapshots.load frame root layout 0 (by decide) body
  have loadLeftHigh := state.snapshots.load frame root layout 1 (by decide) body
  have loadRightLow := state.snapshots.load frame root layout 2 (by decide) body
  have loadRightHigh := state.snapshots.load frame root layout 3 (by decide) body
  have reloadLeftLow := sumState.snapshots.load frame root layout 0 (by decide) body
  have loadSum := lowState.snapshots.load frame root layout 4 (by decide) body
  have reloadLeftHigh := lowState.snapshots.load frame root layout 1 (by decide) body
  cil_contract_steps [found, code, loadLeftLow, loadLeftHigh, loadRightLow, loadRightHigh,
    reloadLeftLow, loadSum, reloadLeftHigh, storeSum, storeLow, storeHigh,
    CIL.Vector.intrinsic_add128, CIL.Vector.intrinsic_lt128, halfSum, halfCarry]
    until continuation after highState

end UInt256Proof.Add.Safety
