import CIL.Safety.SymbolicExecution
import CIL.Safety.Equations
import UInt256.Methods.Add.Vector128Snapshots
import UInt256.Safety.OutputHalves

/-!
Vector128 addition's early output stage: ARM writes both speculative halves to the caller's
output before testing for carry propagation, and SSE branches past the writes.
-/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def earlyOutputCode (adv : Bool) : List CIL.Op := if adv then [
  .arg 2, .skipInit, .feature .advSimd, .brzero 82,
  .arg 2, .memory .asRef, .dup, .local 10, .memory .store128,
  .const32 1, .memory (.add 16 true), .local 11, .memory .store128
] else [
  .arg 2, .skipInit, .feature .advSimd, .brzero 82,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"]

/-- ARM writes both saved result halves to the output; SSE reaches the same position without a
    write. Later states are relative to the memory reached here, whose caller storage differs
    from the original only inside the output. -/
theorem vector128_early_output (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 69 (earlyOutputCode body.profile.advSimd))
    (original entered current : Memory) (inputs outputs : List Reference) (output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (call : CallingConditions program original inputs outputs) (member : output ∈ outputs)
    (argument : args[2]? = some (.reference (.address output)))
    (homes : NumericHomes entered original.nextIdentity specs slots) (value : Nat → BitVec 128)
    (state : VectorState program original.nextIdentity original entered current inputs outputs
      slots value 11)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program original.nextIdentity after entered after inputs outputs slots value
        11 →
      (body.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (value 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (value 10).toNat 16)) →
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) →
      (body.profile.advSimd = false → MemoryBelow original.nextIdentity original after) →
      ∃ fuel result returned,
        run program fuel method 82 args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method 69 args frame [] current = .ok (result, returned) ∧
        post result returned := by
  have formed := state.call.output_formed member
  cases selected : body.profile.advSimd <;> simp only [selected] at code
  · have done := continuation current
      ⟨state.call, .refl _ _, state.authority, state.advanced, state.snapshots⟩
      (by simp [selected]) (fun id offset old _ => state.preserved.cells id old offset)
      (fun _ => state.preserved)
    cil_contract_steps [found, code, argument, formed,
      show body.profile.evaluate .advSimd = false from selected] until done
  · obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
        afterAuthority, outside, privateReads, advanced⟩ :=
      output_halves_update program original entered current inputs outputs output (value 9)
        (value 10) call state.call member state.authority
    have loadLow := state.snapshots.load frame root layout 9 (by decide) body
    have loadHigh := (state.snapshots.transfer homes fun reference fresh bytes loaded =>
      (privateReads reference 16 1 bytes fresh loaded).1).load frame root layout 10 (by decide) body
    have address := middleCall.output_half_address member 1
    simp only [Fin.val_one, Nat.mul_one] at address
    have done := continuation after
      ⟨afterCall, .refl _ _, afterAuthority, Nat.le_trans state.advanced advanced,
        state.snapshots.transfer homes fun reference fresh bytes loaded =>
          (privateReads reference 16 1 bytes fresh loaded).2⟩
      (fun _ => ⟨firstRead, secondRead⟩)
      (fun id offset old excluded =>
        (outside id offset excluded).trans (state.preserved.cells id old offset))
      (by simp [selected])
    cil_contract_steps [found, code, loadLow, loadHigh, argument, formed, firstWrite,
      secondWrite, address, storeValue, referenceAt, ordinaryAccessAlignment,
      show body.profile.evaluate .advSimd = true from selected] until done

end UInt256Proof.Add.Safety
