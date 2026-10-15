import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory
import CIL.SymbolicExecution

namespace UInt256Proof.Compare.PrimitiveLeaf
open CIL.Safety UInt256Model.Safety

def scalarProfile : CIL.FeatureProfile := { architecture := .scalar, nativeWidth := 64, littleEndian := true, advSimd := false, sse2 := false, ssse3 := false, sse42 := false, avx := false, avx2 := false, avx512F := false, avx512FVL := false, bmi1 := false, sse41 := false, avx512DQ := false, avx512DQVL := false, bmi2 := false, armBase64 := false, vector256Accelerated := false }

/-- Expected UInt256 helper bodies. Every gate checks its actual extraction
    against these templates before applying the shared execution theorem. -/
def unsignedForward : CIL.Method := { profile := scalarProfile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 24 8,
  .brnonzero 14,
  .arg 0,
  .fieldAt 16 8,
  .brnonzero 14,
  .arg 0,
  .fieldAt 8 8,
  .brnonzero 14,
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .ltu,
  .ret (some .unsigned8),
  .const32 0,
  .ret (some .unsigned8)] }

def unsignedReverse : CIL.Method := { profile := scalarProfile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 1,
  .fieldAt 24 8,
  .brnonzero 14,
  .arg 1,
  .fieldAt 16 8,
  .brnonzero 14,
  .arg 1,
  .fieldAt 8 8,
  .brnonzero 14,
  .arg 0,
  .arg 1,
  .fieldAt 0 8,
  .ltu,
  .ret (some .unsigned8),
  .const32 1,
  .ret (some .unsigned8)] }

def signedForward : CIL.Method := { profile := scalarProfile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 1,
  .const32 0,
  .convI8,
  .blt 18,
  .arg 0,
  .fieldAt 24 8,
  .brnonzero 18,
  .arg 0,
  .fieldAt 16 8,
  .brnonzero 18,
  .arg 0,
  .fieldAt 8 8,
  .brnonzero 18,
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .ltu,
  .ret (some .unsigned8),
  .const32 0,
  .ret (some .unsigned8)] }

def signedReverse : CIL.Method := { profile := scalarProfile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .const32 0,
  .convI8,
  .blt 18,
  .arg 1,
  .fieldAt 8 8,
  .brnonzero 18,
  .arg 1,
  .fieldAt 16 8,
  .brnonzero 18,
  .arg 1,
  .fieldAt 24 8,
  .brnonzero 18,
  .arg 0,
  .arg 1,
  .fieldAt 0 8,
  .ltu,
  .ret (some .unsigned8),
  .const32 1,
  .ret (some .unsigned8)] }

def method (signed scalarFirst : Bool) : CIL.Method :=
  if signed then if scalarFirst then signedReverse else signedForward
  else if scalarFirst then unsignedReverse else unsignedForward

def result (leafSigned leafScalarFirst : Bool) (memory : Memory) (input : Reference) (word : BitVec 64) : BitVec 32 :=
  if leafSigned && decide (word.toInt < 0) then if leafScalarFirst then 1 else 0
  else if inputLimb memory input 1 = 0 ∧ inputLimb memory input 2 = 0 ∧ inputLimb memory input 3 = 0 then
    if (if leafScalarFirst then word.toNat < (inputLimb memory input 0).toNat
        else (inputLimb memory input 0).toNat < word.toNat) then 1 else 0
  else if leafScalarFirst then 1 else 0

macro "leaf_steps" count:num "with" facts:term,* : tactic =>
  `(tactic| iterate $count:num
    apply Eq.trans
    · apply run_next
      · assumption
      · simp only [method, unsignedForward, unsignedReverse, signedForward, signedReverse]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [method, unsignedForward, unsignedReverse, signedForward, signedReverse, step, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue,
            pureArity, scalars, CIL.step, CIL.binary, CIL.unary, CIL.truth, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, cil_code, $[$facts:term],*]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done)

/-- Prove the helper once for any surrounding program and method index.
    The lookup premise binds the entire body, including profile and frame metadata. -/
theorem run_template (leafSigned leafScalarFirst : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (method leafSigned leafScalarFirst)) (memory : Memory) (input : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program memory [input] []) :
    run program 22 index 0
      (scalarOperatorArguments leafScalarFirst input (.i64 word)) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (result leafSigned leafScalarFirst memory input word))]) := by
  cases signedCase : leafSigned <;> cases firstCase : leafScalarFirst
  all_goals
    simp only [signedCase, firstCase] at found
    have formed := call.input_formed (reference := input) (by simp)
    have constant (value : BitVec 32) (rest : List Value) :
        instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := by rfl
    have fields := fun index rest => call.input_field_instruction (reference := input) (by simp) index rest
    have field0 := fields (0 : Fin 4)
    have field1 := fields (1 : Fin 4)
    have field2 := fields (2 : Fin 4)
    have field3 := fields (3 : Fin 4)
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at field0 field1 field2 field3
    first
      | (have unsigned : leafSigned = false := by simpa only [signedCase]
         by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
         · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
           · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
             · leaf_steps 13 with formed, constant, field0, field1, field2, field3, h1, h2, h3
               simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, h2, h3, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
             · leaf_steps 9 with formed, constant, field0, field1, field2, field3, h1, h2, h3
               simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, h2, h3, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
           · leaf_steps 6 with formed, constant, field0, field1, field2, field3, h3, h2
             simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h3, h2, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
         · leaf_steps 3 with formed, constant, field0, field1, field2, field3, h3
           simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h3, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl))
      | (have signedLeaf : leafSigned = true := by simpa only [signedCase]
         by_cases negative : word.toInt < 0
         · leaf_steps 4 with formed, constant, negative
           simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
         · leaf_steps 4 with formed, constant, negative
           first
             | (have forward : leafScalarFirst = false := by simpa only [firstCase]
                by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
                · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
                  · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
                    · leaf_steps 13 with formed, constant, field0, field1, field2, field3, h1, h2, h3
                      simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
                    · leaf_steps 9 with formed, constant, field0, field1, field2, field3, h1, h2, h3
                      simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
                  · leaf_steps 6 with formed, constant, field0, field1, field2, field3, h3, h2
                    simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h3, h2, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
                · leaf_steps 3 with formed, constant, field0, field1, field2, field3, h3
                  simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl))
             | (have backward : leafScalarFirst = true := by simpa only [firstCase]
                by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
                · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
                  · by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
                    · leaf_steps 13 with formed, constant, field0, field1, field2, field3, h1, h2, h3
                      simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
                    · leaf_steps 9 with formed, constant, field0, field1, field2, field3, h1, h2, h3
                      simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, h2, h3, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
                  · leaf_steps 6 with formed, constant, field0, field1, field2, field3, h1, h2
                    simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, h2, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)
                · leaf_steps 3 with formed, constant, field0, field1, field2, field3, h1
                  simp (config := { implicitDefEqProofs := false }) [run, found, method, unsignedForward, unsignedReverse, signedForward, signedReverse, cil_code, step, constant, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedValue, numericValue, CIL.NarrowKind.extend, result, h1, negative, BitVec.lt_def, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> try (split <;> rfl)))


#print axioms run_template
end UInt256Proof.Compare.PrimitiveLeaf
