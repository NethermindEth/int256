import CIL.Safety.SymbolicExecution
import CIL.Safety.Equations
import UInt256.Methods.Subtract.Vector128Start
import UInt256.Safety.OutputHalves
import CIL.Safety.ReturnMemory

/-!
The fast path of Vector128 subtraction: store both speculative halves through the output view
and return the saved top-lane borrow.
-/

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def subtractFastCode : List CIL.Op := [
  .arg 2, .skipInit, .arg 2, .memory .asRef, .dup,
  .local 5, .local 9, .intrinsic (.vector (.add64 128)) 2, .memory .store128,
  .const32 1, .memory (.add 16 true),
  .local 6, .local 10, .intrinsic (.vector (.add64 128)) 2, .memory .store128,
  .local 8, .const32 1, .intrinsic (.vector (.extract64 128)) 2, .const32 0, .convI8, .gtu,
  .ret (some .unsigned8)]

/-- Store the speculative halves through the checked output view and return the top borrow. -/
theorem subtract_fast_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 119 (subtractFastCode)) (returns : body.returnsValue = true)
    (original entered current : Memory) (inputs outputs : List Reference) (output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value)
    (call : CallingConditions program original inputs outputs) (member : output ∈ outputs)
    (argument : args[2]? = some (.reference (.address output)))
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (values : Fin 4 → BitVec 128)
    (state : VectorState program original.nextIdentity original entered current inputs outputs
      slots (subtractSnapshot values) 10)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 119 args frame [] current = .ok (final, returned) ∧
      final.WellFormed ∧
      returned = [.scalar (.i32 (if lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
      read final output 16 1 =
        .ok (numberBytes (zip128 (· + ·) (subtractSnapshot values 4) (subtractSnapshot values 8)).toNat 16) ∧
      read final { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (zip128 (· + ·) (subtractSnapshot values 5) (subtractSnapshot values 9)).toNat 16) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
      afterAuthority, outside, privateReads, _⟩ :=
    output_halves_update program original entered current inputs outputs output
      (zip128 (· + ·) (subtractSnapshot values 4) (subtractSnapshot values 8))
      (zip128 (· + ·) (subtractSnapshot values 5) (subtractSnapshot values 9))
      call state.call member state.authority
  have middleSnapshots := state.snapshots.transfer homes
    (fun reference fresh bytes loaded => (privateReads reference 16 1 bytes fresh loaded).1)
  have afterSnapshots := state.snapshots.transfer homes
    (fun reference fresh bytes loaded => (privateReads reference 16 1 bytes fresh loaded).2)
  have a4 := state.snapshots.load frame root layout 4 (by decide) body
  have a8 := state.snapshots.load frame root layout 8 (by decide) body
  have b5 := middleSnapshots.load frame root layout 5 (by decide) body
  have b9 := middleSnapshots.load frame root layout 9 (by decide) body
  have c7 := afterSnapshots.load frame root layout 7 (by decide) body
  have formed := state.call.output_formed member
  have address := middleCall.output_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at address
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  cil_contract_steps [found, code, returns, a4, a8, b5, b9, c7, argument, formed, firstWrite,
    secondWrite, address, storeValue, referenceAt, ordinaryAccessAlignment, intrinsic_add128,
    intrinsic_extract128]
  refine ⟨leaveFrame_preserves_wellFormed _ _ afterCall.1.1, ?_,
    (teardown.read output old 16 1).trans firstRead,
    (teardown.read { output with offset := output.offset + 16 } old 16 1).trans secondRead,
    (teardown.access output old 32 1 true).trans
      (afterCall.1.writable (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩)), ?_⟩
  · rw [CIL.NarrowKind.extend_ite_ofNat_one_zero]; rfl
  · intro id offset earlier untouched
    exact (teardown.cells id earlier offset).trans ((outside id offset untouched).trans
      (state.preserved.cells id earlier offset))

end UInt256Proof.Subtract.Profile
