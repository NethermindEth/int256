import UInt256.Methods.Compare.PortableSafetyLocals
import UInt256.Methods.Compare.MaskSafety
import UInt256.Methods.Compare.VectorMasks
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def portableEqual (left right : BitVec 256) : BitVec 32 :=
  CIL.Vector.moveMask64 (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) left right)
def portableLess (left right : BitVec 256) : BitVec 32 :=
  CIL.Vector.moveMask64 (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x.ult y)) left right)

theorem portable_run (memory : Memory) (left right : Reference) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower portableSpecs frame.locals)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel final,
      run Extracted.program fuel portableIndex 0 (readOnlyArguments [left, right]) frame [] memory =
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
  have found : Extracted.program[portableIndex]? = some portableBody := by rfl
  have fetched : portableBody.code[18]? = some (.call maskIndex 2) := by rfl
  have returned : portableBody.code[19]? = some .ret := by rfl
  have returns : portableBody.returnsValue = true := by rfl
  have stepped : step portableBody (.call maskIndex 2) 18 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 ltWord), .scalar (.i32 eqWord)] m2 =
      .ok (.call maskIndex [.scalar (.i32 eqWord), .scalar (.i32 ltWord)] [] m2) := by
    simp [step, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run Extracted.program 1 portableIndex 19 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (maskResult eqWord ltWord))] m2 =
      .ok (leaveFrame frame m2, [.scalar (.i32 (maskResult eqWord ltWord))]) := by
    simp [run, found, returned, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨8, mask_invoke m2 eqWord ltWord⟩ ⟨1, tail⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := call.input_load (reference := left) (by simp)
  have hr := call.input_load (reference := right) (by simp)
  simp only [eqWord, ltWord, portableEqual, portableLess, x, y] at s1 s2 r1 r2 tail
  refine ⟨tailFuel + 18, m2, ?_, preserved⟩
  conv in portableIndex => cbv
  iterate 18
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr, hl, hr,
            slot0, slot1, slot2, duplicate, s0, s1, s2, r0, r0after, r1, r2, keep0, keep1, keep2, x, y,
            pureArity, scalars, staticInstruction, memoryInstruction,
            CIL.step, CIL.Intrinsic.available, intrinsic_portable_eq, intrinsic_portable_lt,
            intrinsic_portable_mask, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  exact tail

#print axioms portable_run
end UInt256Proof.Compare.Safety
