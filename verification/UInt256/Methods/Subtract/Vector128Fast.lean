import CIL.Safety.Equations
import UInt256.Methods.Subtract.Vector128Start
import UInt256.Safety.OutputHalves
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Profile
def subtractFastCode : List CIL.Op := [
  .arg 2, .skipInit, .arg 2, .memory .asRef, .dup,
  .local 5, .local 9, .intrinsic (.vector (.add64 128)) 2, .memory .store128,
  .const32 1, .memory (.add 16 true),
  .local 6, .local 10, .intrinsic (.vector (.add64 128)) 2, .memory .store128,
  .local 8, .const32 1, .intrinsic (.vector (.extract64 128)) 2, .const32 0, .convI8, .gtu,
  .ret (some .unsigned8)]
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- The fast suffix returns the saved top-lane borrow mask and retires its frame. -/
theorem subtract_fast_return (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 119)
    (code : body.code = leading ++ subtractFastCode ++ tail) (returns : body.returnsValue = true)
    (memory : Memory) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (values : Fin 4 → BitVec 128) (snapshots : SubtractSnapshots memory slots values 10) :
    run program 7 method 134 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0 then 1 else 0))]) := by
  have load := snapshots.load frame root layout 7 (by decide) body
  iterate 6
    apply Eq.trans
    · apply run_next found (by simp [code, List.getElem?_append, leadingLength, subtractFastCode]; rfl)
      first
      | exact load _ _ _
      | (simp (config := { implicitDefEqProofs := false })
          [checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def, CIL.binary,
            CIL.Intrinsic.available, CIL.Vector.intrinsic_extract128,
            checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : body.code[140]? = some (.ret (some .unsigned8)) := by
    simp [code, List.getElem?_append, leadingLength, subtractFastCode]
  by_cases borrow : lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend, borrow,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Store the speculative halves through the checked output view and return the top borrow. -/
theorem subtract_fast_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 119)
    (code : body.code = leading ++ subtractFastCode ++ tail) (returns : body.returnsValue = true)
    (vectorSpecs : ∀ i : Fin 10, specs[i.val]? = some vector128ZeroSpec)
    (original entered current : Memory) (inputs outputs : List Reference) (output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value)
    (call : CallingConditions program original inputs outputs) (member : output ∈ outputs)
    (argument : args[2]? = some (.reference (.address output)))
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (values : Fin 4 → BitVec 128)
    (state : SubtractVectorState program original entered current inputs outputs slots values 10)
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
  have middleSnapshots := state.snapshots.transfer homes vectorSpecs
    (fun reference fresh bytes loaded => (privateReads reference 16 1 bytes fresh loaded).1)
  have afterSnapshots := state.snapshots.transfer homes vectorSpecs
    (fun reference fresh bytes loaded => (privateReads reference 16 1 bytes fresh loaded).2)
  have a4 := state.load frame root layout 4 (by decide) body
  have a8 := state.load frame root layout 8 (by decide) body
  have b5 := middleSnapshots.load frame root layout 5 (by decide) body
  have b9 := middleSnapshots.load frame root layout 9 (by decide) body
  have formed := state.call.output_formed member
  have address := middleCall.output_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at address
  have returned := subtract_fast_return program body method found leading tail leadingLength code returns
    after frame root slots layout args values afterSnapshots
  let post : Memory → List Value → Prop := fun final values' =>
    final = leaveFrame frame after ∧
      values' = [.scalar (.i32 (if lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0 then 1 else 0))]
  have done : ∃ fuel result values', run program fuel method 134 args frame [] after = .ok (result, values') ∧
      post result values' := ⟨7, _, _, returned, rfl, rfl⟩
  have executed : ∃ fuel result values', run program fuel method 119 args frame [] current =
      .ok (result, values') ∧ post result values' := by
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, subtractFastCode]; rfl)
         first
         | exact a4 _ _ _
         | exact a8 _ _ _
         | exact b5 _ _ _
         | exact b9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, step, argument, checkedValue, formValue, formed, instruction, staticInstruction,
               memoryInstruction, storeValue, referenceAt, firstWrite, secondWrite, address, CIL.offsetValue,
               checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_add128, numericValue,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  obtain ⟨fuel, final, values', run, sameFinal, sameValues⟩ := executed
  subst sameFinal
  subst sameValues
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  refine ⟨fuel, _, _, run, leaveFrame_preserves_wellFormed _ _ afterCall.1.1, rfl,
    (teardown.read output old 16 1).trans firstRead,
    (teardown.read { output with offset := output.offset + 16 } old 16 1).trans secondRead,
    (teardown.access output old 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩)), ?_⟩
  intro id offset earlier untouched
  exact (teardown.cells id earlier offset).trans ((outside id offset untouched).trans
    (state.preserved.cells id earlier offset))

#print axioms subtract_fast_return
#print axioms subtract_fast_checked
end UInt256Proof.Subtract.Profile
