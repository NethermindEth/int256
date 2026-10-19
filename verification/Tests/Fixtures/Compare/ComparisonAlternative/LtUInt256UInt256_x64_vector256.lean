import UInt256.Methods.Compare.PortableSafetyContract
import UInt256.Methods.Compare.PortableLocals
import UInt256.Methods.Compare.MaskSafety
import UInt256.Methods.Compare.VectorMasks
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyForwarder
import UInt256.Methods.Compare.WrapperSafetyContract
import UInt256.Safety.ProfileContracts

namespace CompareFixture
open CIL.Safety UInt256Proof.Compare.Safety

/-- Mask reduction with the shifted less-than mask as the first addend. -/
def altMaskBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 1,
  .const32 1,
  .shl,
  .arg 0,
  .add,
  .const32 (BitVec.ofInt 32 (15)),
  .gtu,
  .ret (some .unsigned8)] }

theorem alt_mask_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat) (found : program[index]? = some (altMaskBody profile)) (memory : CIL.Safety.Memory) (equal less : BitVec 32) :
    CIL.Safety.invoke program 8 index [.scalar (.i32 equal), .scalar (.i32 less)] memory =
      .ok (memory, [.scalar (.i32 (maskResult equal less))]) := by
  rw [show maskResult equal less = if 15 < ((less <<< 1) + equal).toNat then 1 else 0 by
    simp only [maskResult, BitVec.add_comm]]
  split <;> rename_i condition
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.mod_add_mod] at condition
  all_goals simp only [show (2 : Nat)^32 = 4294967296 from rfl] at condition
  all_goals simp [CIL.Safety.invoke, CIL.Safety.run, found, altMaskBody, enterFrame, makeLocals, makeArgumentHomes, makeParameterHomes, leaveFrame,
    CIL.Safety.step, CIL.Safety.instruction, checkedValue, numericValue, pureArity, scalars,
    CIL.step, CIL.NarrowKind.extend, condition, CIL.binary, BitVec.lt_def,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms alt_mask_invoke
end CompareFixture

namespace CompareFixture
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare UInt256Proof.Compare.Safety

theorem alt_portable_run (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat) (found : program[index]? = some (portableBody profile callee)) (maskFound : program[callee]? = some (altMaskBody profile)) (memory : Memory) (left right : Reference) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower portableSpecs frame.locals)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
        .ok (leaveFrame frame final, [.scalar (.i32 (maskResult
          (portableEqual (inputValue memory left) (inputValue memory right))
          (portableLess (inputValue memory left) (inputValue memory right))))]) ∧
      MemoryBelow lower memory final := by
  let x := inputValue memory left
  let y := inputValue memory right
  let eqWord := portableEqual x y
  let ltWord := portableLess x y
  obtain ⟨vr, er, lr, m0, m1, m2, slots, s0, s1, s2, r0, r0after, r1, r2, _, _, preserved⟩ :=
    portable_local_writes memory frame lower homes y eqWord ltWord
  have slot0 : frame.locals[0]? = some (.bytes .vector256 vr) := by simp [slots]
  have slot1 : frame.locals[1]? = some (.bytes .word32 er) := by simp [slots]
  have slot2 : frame.locals[2]? = some (.bytes .word32 lr) := by simp [slots]
  have duplicate (m : Memory) (bits : BitVec 256) (rest : List Value) :
      instruction .dup (.scalar (.v256 bits) :: rest) m =
        .ok (m, .scalar (.v256 bits) :: .scalar (.v256 bits) :: rest) := by
    simp [instruction, checkedValue, numericValue, Pure.pure, Except.pure]
  have keep0 : frame.locals.set 0 (.bytes .vector256 vr) = frame.locals := by simp [slots]
  have keep1 : frame.locals.set 1 (.bytes .word32 er) = frame.locals := by simp [slots]
  have keep2 : frame.locals.set 2 (.bytes .word32 lr) = frame.locals := by simp [slots]

  have fetched : (portableBody profile callee).code[18]? = some (.call callee 2) := by rfl
  have returned : (portableBody profile callee).code[19]? = some (.ret (some .unsigned8)) := by rfl
  have returns : (portableBody profile callee).returnsValue = true := by rfl
  have stepped : step (portableBody profile callee) (.call callee 2) 18 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 ltWord), .scalar (.i32 eqWord)] m2 =
      .ok (.call callee [.scalar (.i32 eqWord), .scalar (.i32 ltWord)] [] m2) := by
    simp [step, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run program 1 index 19 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (maskResult eqWord ltWord))] m2 =
      .ok (leaveFrame frame m2, [.scalar (.i32 (maskResult eqWord ltWord))]) := by
    simp [run, found, returned, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    unfold maskResult
    split <;> simp [CIL.NarrowKind.extend]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨8, alt_mask_invoke profile program callee maskFound m2 eqWord ltWord⟩ ⟨1, tail⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := UInt256Proof.Equality.VectorPrimitive.load_input call (by simp : left ∈ [left, right])
  have cl := UInt256Proof.Equality.VectorPrimitive.cast_input memory left
  have hr := UInt256Proof.Equality.VectorPrimitive.load_input call (by simp : right ∈ [left, right])
  have cr := UInt256Proof.Equality.VectorPrimitive.cast_input memory right
  simp only [eqWord, ltWord, portableEqual, portableLess, x, y] at *
  clear eqWord ltWord x y
  generalize leftValue : inputValue memory left = leftBits at *
  generalize rightValue : inputValue memory right = rightBits at *
  refine ⟨tailFuel + 18, m2, ?_, preserved⟩

  iterate 18
    apply Eq.trans
    · apply run_next found
      · simp only [portableBody]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, checkedIntrinsic, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr, hl, hr, cl, cr,
            slot0, slot1, slot2, duplicate, s0, s1, s2, r0, r0after, r1, r2, keep0, keep1, keep2,
            pureArity, scalars, staticInstruction,
            CIL.step.eq_def, CIL.Intrinsic.available, intrinsic_portable_eq, intrinsic_portable_lt,
            intrinsic_portable_mask, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  exact tail

#print axioms alt_portable_run
end CompareFixture

namespace CompareFixture
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare UInt256Proof.Compare.Safety

theorem alt_portable_checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat) (found : program[index]? = some (portableBody profile callee)) (maskFound : program[callee]? = some (altMaskBody profile)) : BinaryReadOnlyInvocation
    (fun left right => .i32 (if left.toNat < right.toNat then 1 else 0))
    program index := by
  intro memory left right call
  obtain ⟨frame, entered, setup, homes, enteredCall, before⟩ := portable_setup profile callee program memory left right call
  obtain ⟨fuel, final, finished, preserved⟩ := alt_portable_run profile program index callee found maskFound entered left right frame memory.nextIdentity homes enteredCall
  rw [portable_result_math, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
    call.input_value_after_setup setup (by simp : right ∈ [left, right])] at finished

  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame final memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((preserved.cells id bound offset).trans (before.cells id bound offset))

#print axioms alt_portable_checked
end CompareFixture

open UInt256Model.Safety UInt256Proof.Compare.Safety in
/-- Vector-path comparison whose mask helper adds the shifted less-than mask first. -/
theorem CompareFixture.correct :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  have entry : BinaryReadOnlyInvocation lessValue Extracted.program Extracted.entryIndex :=
    entry_checked (alt_portable_checked Extracted.profile Extracted.program wrapperLeafIndex (wrapperLeafIndex + 1) rfl rfl)
  simpa only [lessValue] using entry.to_contract

#print axioms CompareFixture.correct
