import UInt256.Methods.Compare.NativeSafetyLocals
import UInt256.Methods.Compare.VectorMasks
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def nativeEqual (left right : BitVec 256) : BitVec 256 :=
  (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) left right)
def nativeComparison (left right : BitVec 256) : BitVec 256 :=
  (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (if nativeUsesLess then x.ult y else y.ult x)) left right)

def nativeResult (left right : BitVec 256) : BitVec 32 :=
  if ((CIL.Vector.moveMask32 (CIL.Vector.blend32 (nativeEqual left right)
      (nativeComparison left right) 170)) - (if nativeInclusive then 86 else 85)).toInt < 0 then 1 else 0

macro "native_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, readOnlyArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, staticInstruction, memoryInstruction,
            CIL.step, CIL.Intrinsic.available, intrinsic_native_eq, intrinsic_native_lt, intrinsic_native_gt,
            intrinsic_native_mask, intrinsic_avx2_blend, intrinsic_avx_blend, intrinsic_reinterpret256,
            CIL.FeatureProfile.evaluate, CIL.truth, CIL.binary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

theorem native_run (memory : Memory) (left right : Reference) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower nativeSpecs frame.locals)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel final,
      run Extracted.program fuel nativeIndex 0 (readOnlyArguments [left, right]) frame [] memory =
        .ok (leaveFrame frame final, [.scalar (.i32 (nativeResult (inputValue memory left) (inputValue memory right)))]) ∧
      MemoryBelow lower memory final := by
  let x := inputValue memory left
  let y := inputValue memory right
  let eqWord := nativeEqual x y
  let ltWord := nativeComparison x y
  obtain ⟨vr, er, lr, m0, m1, m2, slots, s0, s1, s2, r0, r0after, r1, r2, _, _, preserved⟩ :=
    native_local_writes memory frame lower homes y eqWord ltWord
  have slot0 : frame.locals[0]? = some (.bytes .vector256 vr) := by simp [slots]
  have slot1 : frame.locals[1]? = some (.bytes .vector256 er) := by simp [slots]
  have slot2 : frame.locals[2]? = some (.bytes .vector256 lr) := by simp [slots]
  have duplicate (m : Memory) (bits : BitVec 256) (rest : List Value) :
      instruction .dup (.scalar (.v256 bits) :: rest) m =
        .ok (m, .scalar (.v256 bits) :: .scalar (.v256 bits) :: rest) := by
    simp [instruction, checkedValue, numericValue, Pure.pure, Except.pure]
  have constant (m : Memory) (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest m = .ok (m, .scalar (.i32 value) :: rest) := by rfl
  have keep0 : frame.locals.set 0 (.bytes .vector256 vr) = frame.locals := by simp [slots]
  have keep1 : frame.locals.set 1 (.bytes .vector256 er) = frame.locals := by simp [slots]
  have keep2 : frame.locals.set 2 (.bytes .vector256 lr) = frame.locals := by simp [slots]
  have found : Extracted.program[nativeIndex]? = some nativeBody := by rfl
  have returned : nativeBody.code[nativeReturn]? = some .ret := by rfl
  have returns : nativeBody.returnsValue = true := by rfl
  have tail : run Extracted.program 1 nativeIndex nativeReturn (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (nativeResult x y))] m2 =
      .ok (leaveFrame frame m2, [.scalar (.i32 (nativeResult x y))]) := by
    simp [run, found, returned, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := call.input_load (reference := left) (by simp)
  have hr := call.input_load (reference := right) (by simp)
  have direction : nativeUsesLess = nativeUsesLess := rfl
  conv at direction => rhs; cbv
  have inclusive : nativeInclusive = nativeInclusive := rfl
  conv at inclusive => rhs; cbv
  have returnPosition : nativeReturn = nativeReturn := rfl
  conv at returnPosition => rhs; cbv
  have index : nativeIndex = nativeIndex := rfl
  conv at index => rhs; cbv
  simp only [eqWord, ltWord, nativeEqual, nativeComparison, nativeResult,
    direction, inclusive,
    Bool.false_eq_true, Bool.true_eq, ite_true, ite_false, x, y] at s1 s2 r1 r2 tail
  simp [index, returnPosition] at tail
  refine ⟨nativeReturn + 1, m2, ?_, preserved⟩
  conv in nativeReturn => cbv
  conv in nativeIndex => cbv
  first
  | (native_steps 27 with fl, fr, hl, hr, slot0, slot1, slot2, duplicate, constant, s0, s1, s2, r0, r0after, r1, r2, keep0, keep1, keep2, x, y
     simpa [direction, inclusive, nativeResult, nativeEqual, nativeComparison] using tail)
  | (native_steps 28 with fl, fr, hl, hr, slot0, slot1, slot2, duplicate, constant, s0, s1, s2, r0, r0after, r1, r2, keep0, keep1, keep2, x, y
     simpa [direction, inclusive, nativeResult, nativeEqual, nativeComparison] using tail)

#print axioms native_run
end UInt256Proof.Compare.Safety
