import UInt256.Methods.Compare.PortableLocals
import UInt256.Methods.Compare.MaskSafety
import UInt256.Methods.Compare.VectorMasks
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyForwarder
namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety
def portableEqual (left right : BitVec 256) : BitVec 32 :=
  CIL.Vector.moveMask64 (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) left right)
def portableLess (left right : BitVec 256) : BitVec 32 :=
  CIL.Vector.moveMask64 (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x.ult y)) left right)

theorem portable_run (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat) (found : program[index]? = some (portableBody profile callee)) (maskFound : program[callee]? = some (maskBody profile)) (memory : Memory) (left right : Reference) (frame : Frame) (lower : Nat)
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
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨8, mask_invoke profile program callee maskFound m2 eqWord ltWord⟩ ⟨1, tail⟩
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

#print axioms portable_run
end UInt256Proof.Compare.Safety

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

theorem portable_result_math (memory : Memory) (left right : Reference) :
    maskResult (portableEqual (inputValue memory left) (inputValue memory right))
      (portableLess (inputValue memory left) (inputValue memory right)) =
      if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  simp only [portableEqual, portableLess, portableEqualityMask, portableLessMask, mask_result_math]

theorem portable_checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat) (found : program[index]? = some (portableBody profile callee)) (maskFound : program[callee]? = some (maskBody profile)) : BinaryReadOnlyInvocation
    (fun left right => .i32 (if left.toNat < right.toNat then 1 else 0))
    program index := by
  intro memory left right call
  obtain ⟨frame, entered, setup, homes, enteredCall, before⟩ := portable_setup profile callee program memory left right call
  obtain ⟨fuel, final, finished, preserved⟩ := portable_run profile program index callee found maskFound entered left right frame memory.nextIdentity homes enteredCall
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

#print axioms portable_result_math
#print axioms portable_checked
end UInt256Proof.Compare.Safety
