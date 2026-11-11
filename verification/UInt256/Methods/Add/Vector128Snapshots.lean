import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.Vector128Start
import UInt256.Methods.AddSubtract.Vector128Incoming

/-!
Vector128 addition's speculative results: each lane sum minus its incoming carry mask, and the
values of the eleven private vectors saved by then.
-/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def correctionCode : List CIL.Op := [.local 8, .intrinsic (.vector (.sub64 128)) 2, .setLocal 10,
  .local 5, .local 9, .intrinsic (.vector (.sub64 128)) 2, .setLocal 11]

/-- Subtract each incoming all-ones carry mask and store both speculative result halves. -/
theorem vector128_correction_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 62 correctionCode)
    (lowSpec : specs[9]? = some vector128ZeroSpec) (highSpec : specs[10]? = some vector128ZeroSpec)
    (boundary : Nat) (origin entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots) (value : Nat → BitVec 128)
    (low : BitVec 128) (lowResult : value 9 = corrected128 low (value 7))
    (highResult : value 10 = corrected128 (value 4) (value 8))
    (state : VectorState program boundary origin entered current inputs outputs slots value 9)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program boundary origin entered after inputs outputs slots value 11 →
      ∃ fuel result returned,
        run program fuel method 69 args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method 62 args frame [.scalar (.v128 low)] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨middle, lowState, storeLow⟩ :=
    state.store body specs frame root layout enteredWF homes lowSpec _ lowResult
  obtain ⟨after, highState, storeHigh⟩ :=
    lowState.store body specs frame root layout enteredWF homes highSpec _ highResult
  have loadIncoming := state.snapshots.load frame root layout 7 (by decide) body
  have loadSum := lowState.snapshots.load frame root layout 4 (by decide) body
  have loadHighIncoming := lowState.snapshots.load frame root layout 8 (by decide) body
  cil_contract_steps [found, code, loadIncoming, loadSum, loadHighIncoming, storeLow, storeHigh,
    intrinsic_sub128, corrected128] until continuation after highState

/-- Initial operands and the exact saved vectors at the output-stage boundary. -/
def vector128SnapshotValue (memory : Memory) (left right : Reference) (i : Fin 11) : BitVec 128 :=
  let a := inputHalf memory left 0
  let b := inputHalf memory left 1
  let c := inputHalf memory right 0
  let d := inputHalf memory right 1
  let low := halfSum a c
  let high := halfSum b d
  let lowMask := halfCarry low a
  let highMask := halfCarry high b
  match i.val with
  | 0 => a | 1 => b | 2 => c | 3 => d
  | 4 => high | 5 => lowMask | 6 => highMask
  | 7 => incoming128Low lowMask | 8 => incoming128High lowMask highMask
  | 9 => corrected128 low (incoming128Low lowMask)
  | _ => corrected128 high (incoming128High lowMask highMask)

end UInt256Proof.Add.Safety
