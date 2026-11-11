import CIL.Safety.SymbolicExecution
import CIL.Safety.Equations
import CIL.Safety.ReturnMemory
import UInt256.Methods.Add.Vector128Decision

/-!
The fast suffix of Vector128 addition: SSE writes both saved result halves, which ARM wrote
before the decision, and both return the saved high-lane carry.
-/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def fastOutputCode (adv : Bool) : List CIL.Op := if adv then [
  .feature .advSimd, .brnonzero 215,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 7, .const32 1, .intrinsic (.vector (.extract64 128)) 2, .const32 0, .convI8, .gtu,
  .ret (some .unsigned8)
] else [
  .feature .advSimd, .brnonzero 215,
  .arg 2, .memory .asRef, .dup, .local 10, .memory .store128,
  .const32 1, .memory (.add 16 true), .local 11, .memory .store128,
  .local 7, .const32 1, .intrinsic (.vector (.extract64 128)) 2, .const32 0, .convI8, .gtu,
  .ret (some .unsigned8)]

/-- The fast suffix leaves both saved result halves in the output, changes no other caller
    byte and returns the saved high-lane carry bit. -/
theorem vector128_fast_suffix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 204 (fastOutputCode body.profile.advSimd))
    (returns : body.returnsValue = true) (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (homes : NumericHomes entered original.nextIdentity specs slots) (value : Nat → BitVec 128)
    (snapshots : VectorSnapshots current slots value 11)
    (earlyRead : body.profile.advSimd = true →
      read current output 16 1 = .ok (numberBytes (value 9).toNat 16) ∧
      read current { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (value 10).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 16 1 = .ok (numberBytes (value 9).toNat 16) →
      read after { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (value 10).toNat 16) →
      CallingConditions program after inputs outputs →
      (∀ id offset, OutsideOutput output id offset →
        after.cells id offset = current.cells id offset) →
      post (leaveFrame frame after)
        [.scalar (.i32 (if lane64 (value 6) 1 > BitVec.ofNat 64 0 then 1 else 0))]) :
    ∃ fuel result returned,
      run program fuel method 204 args frame [] current = .ok (result, returned) ∧
        post result returned := by
  cases selected : body.profile.advSimd <;> simp only [selected] at code
  · obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
        _, outside, privateReads, _⟩ :=
      output_halves_update program original entered current inputs outputs output (value 9)
        (value 10) call currentCall member authority
    have loadLow := snapshots.load frame root layout 9 (by decide) body
    have loadHigh := (snapshots.transfer homes fun reference fresh bytes loaded =>
      (privateReads reference 16 1 bytes fresh loaded).1).load frame root layout 10 (by decide) body
    have loadCarry := (snapshots.transfer homes fun reference fresh bytes loaded =>
      (privateReads reference 16 1 bytes fresh loaded).2).load frame root layout 6 (by decide) body
    have formed := currentCall.output_formed member
    have address := middleCall.output_half_address member 1
    simp only [Fin.val_one, Nat.mul_one] at address
    cil_contract_steps [found, code, returns, loadLow, loadHigh, loadCarry, argument, formed,
      firstWrite, secondWrite, address, storeValue, referenceAt, ordinaryAccessAlignment,
      intrinsic_extract128, show body.profile.evaluate .advSimd = false from selected]
    rw [CIL.NarrowKind.extend_ite_ofNat_one_zero]
    exact continuation after firstRead secondRead afterCall outside
  · have loadCarry := snapshots.load frame root layout 6 (by decide) body
    cil_contract_steps 2 [found, code, show body.profile.evaluate .advSimd = true from selected]
    -- The taken feature branch leaves its target as an undecided literal comparison.
    simp only [BitVec.reduceEq, not_false_eq_true, ↓reduceIte]
    cil_contract_steps [found, code, returns, loadCarry, intrinsic_extract128]
    rw [CIL.NarrowKind.extend_ite_ofNat_one_zero]
    exact continuation current (earlyRead selected).1 (earlyRead selected).2 currentCall
      (fun _ _ _ => rfl)

end UInt256Proof.Add.Safety
