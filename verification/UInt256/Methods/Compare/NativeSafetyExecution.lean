import UInt256.Methods.Compare.NativeLocals
import UInt256.Methods.Compare.VectorMasks
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety
def nativeEqual (left right : BitVec 256) : BitVec 256 :=
  (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) left right)
def nativeComparison (usesLess : Bool) (left right : BitVec 256) : BitVec 256 :=
  (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (if usesLess then x.ult y else y.ult x)) left right)

def nativeResult (usesLess inclusive : Bool) (left right : BitVec 256) : BitVec 32 :=
  if ((CIL.Vector.moveMask32 (CIL.Vector.blend32 (nativeEqual left right)
      (nativeComparison usesLess left right) 170)) - (if inclusive then 86 else 85)).toInt < 0 then 1 else 0

macro "native_steps" count:num "using" lookup:term "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next $lookup
      · simp only [nativeBody]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [nativeBody, step, checkedIntrinsic, readOnlyArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, staticInstruction,
            CIL.step.eq_def, CIL.Intrinsic.available, intrinsic_native_eq, intrinsic_native_lt, intrinsic_native_gt,
            intrinsic_native_mask, intrinsic_avx2_blend, intrinsic_avx_blend, intrinsic_reinterpret256,
            CIL.FeatureProfile.evaluate, CIL.truth, CIL.binary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

theorem native_run (profile : CIL.FeatureProfile) (usesLess inclusive : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (nativeBody profile usesLess inclusive))
    (native : profile.avx512FVL = true) (nativeF : profile.avx512F = true) (avx2 : profile.avx2 = true) (avx : profile.avx = true)
    (memory : Memory) (left right : Reference) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower nativeSpecs frame.locals)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
        .ok (leaveFrame frame final, [.scalar (.i32 (nativeResult usesLess inclusive (inputValue memory left) (inputValue memory right)))]) ∧
      MemoryBelow lower memory final := by
  let x := inputValue memory left
  let y := inputValue memory right
  let eqWord := nativeEqual x y
  let ltWord := nativeComparison usesLess x y
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
      instruction (.const32 value) rest m = .ok (m, .scalar (.i32 value) :: rest) := by cases inclusive <;> rfl
  have keep0 : frame.locals.set 0 (.bytes .vector256 vr) = frame.locals := by simp [slots]
  have keep1 : frame.locals.set 1 (.bytes .vector256 er) = frame.locals := by simp [slots]
  have keep2 : frame.locals.set 2 (.bytes .vector256 lr) = frame.locals := by simp [slots]

  have returned : (nativeBody profile usesLess inclusive).code[(if inclusive then 28 else 27)]? = some (.ret (some .unsigned8)) := by cases inclusive <;> rfl
  have returns : (nativeBody profile usesLess inclusive).returnsValue = true := by cases inclusive <;> rfl
  have tail : run program 1 index (if inclusive then 28 else 27) (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (nativeResult usesLess inclusive x y))] m2 =
      .ok (leaveFrame frame m2, [.scalar (.i32 (nativeResult usesLess inclusive x y))]) := by
    simp [run, found, returned, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    unfold nativeResult
    split <;> simp [CIL.NarrowKind.extend]
    all_goals split <;> rfl
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := UInt256Proof.Equality.VectorPrimitive.load_input call (by simp : left ∈ [left, right])
  have cl := UInt256Proof.Equality.VectorPrimitive.cast_input memory left
  have hr := UInt256Proof.Equality.VectorPrimitive.load_input call (by simp : right ∈ [left, right])
  have cr := UInt256Proof.Equality.VectorPrimitive.cast_input memory right
  simp only [eqWord, ltWord, nativeEqual, nativeComparison, x, y] at *
  clear eqWord ltWord x y
  generalize leftValue : inputValue memory left = leftBits at *
  generalize rightValue : inputValue memory right = rightBits at *
  refine ⟨(if inclusive then 28 else 27) + 1, m2, ?_, preserved⟩
  cases direction : usesLess <;> cases mode : inclusive
  all_goals
    simp only [direction, mode, Bool.false_eq_true, Bool.true_eq, ite_true, ite_false] at *
    first
    | (native_steps 27 using found with native, nativeF, avx2, avx, fl, fr, hl, hr, cl, cr, slot0, slot1, slot2, duplicate, constant, s0, s1, s2, r0, r0after, r1, r2, keep0, keep1, keep2
       simpa [nativeResult, nativeEqual, nativeComparison] using tail)
    | (native_steps 28 using found with native, nativeF, avx2, avx, fl, fr, hl, hr, cl, cr, slot0, slot1, slot2, duplicate, constant, s0, s1, s2, r0, r0after, r1, r2, keep0, keep1, keep2
       simpa [nativeResult, nativeEqual, nativeComparison] using tail)
#print axioms native_run
end UInt256Proof.Compare.Safety
