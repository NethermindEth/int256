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

private theorem checked_reference {memory : Memory} {input : Reference}
    (formed : form memory input = .ok input) :
    checkedValue memory (.reference (.address input)) = .ok (.reference (.address input)) := by
  simp only [checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

private theorem step_arg_first {body : CIL.Method} {pc : Nat} {rest stack : List Value} {frame : Frame}
    {memory : Memory} {input : Reference} (formed : form memory input = .ok input) :
    step body (.arg 0) pc (.reference (.address input) :: rest) frame stack memory =
      .ok (.next (pc + 1) (.reference (.address input) :: stack) frame memory) := by
  show (checkedValue memory (.reference (.address input))).bind _ = _
  rw [checked_reference formed]; rfl

private theorem step_arg_second {body : CIL.Method} {pc : Nat} {first : Value} {rest stack : List Value}
    {frame : Frame} {memory : Memory} {input : Reference} (formed : form memory input = .ok input) :
    step body (.arg 1) pc (first :: .reference (.address input) :: rest) frame stack memory =
      .ok (.next (pc + 1) (.reference (.address input) :: stack) frame memory) := by
  show (checkedValue memory (.reference (.address input))).bind _ = _
  rw [checked_reference formed]; rfl

private theorem step_field {body : CIL.Method} {pc offset : Nat} {args rest values : List Value}
    {frame : Frame} {memory : Memory} {reference : ManagedReference}
    (loaded : instruction (.fieldAt offset 8) (.reference reference :: rest) memory = .ok (memory, values)) :
    step body (.fieldAt offset 8) pc args frame (.reference reference :: rest) memory =
      .ok (.next (pc + 1) values frame memory) := by
  have unfolded : step body (.fieldAt offset 8) pc args frame (.reference reference :: rest) memory =
      (instruction (.fieldAt offset 8) (.reference reference :: rest) memory).bind
        fun result => .ok (.next (pc + 1) result.2 frame result.1) := rfl
  rw [unfolded, loaded]; rfl

private theorem step_brnonzero_zero {body : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {x : BitVec 64} (zero : x = BitVec.ofNat 64 0) :
    step body (.brnonzero target) pc args frame (.scalar (.i64 x) :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := by
  subst zero; rfl

private theorem step_brnonzero_ne {body : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {x : BitVec 64} (nonzero : ¬x = BitVec.ofNat 64 0) :
    step body (.brnonzero target) pc args frame (.scalar (.i64 x) :: rest) memory =
      .ok (.next target rest frame memory) := by
  have unfolded : step body (.brnonzero target) pc args frame (.scalar (.i64 x) :: rest) memory =
      .ok (.next (if (x != 0) = true then target else pc + 1) rest frame memory) := rfl
  rw [unfolded, ite_eq_left (by simpa using nonzero)]

private theorem step_convI8_zero {body : CIL.Method} {pc : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} :
    step body .convI8 pc args frame (.scalar (.i32 0) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i64 0) :: rest) frame memory) := rfl

private theorem step_blt_zero {body : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {word : BitVec 64} :
    step body (.blt target) pc args frame (.scalar (.i64 0) :: .scalar (.i64 word) :: rest) memory =
      .ok (.next (if word.toInt < (0 : BitVec 64).toInt then target else pc + 1) rest frame memory) := rfl

private theorem step_blt_neg {body : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {word : BitVec 64} (negative : word.toInt < 0) :
    step body (.blt target) pc args frame (.scalar (.i64 0) :: .scalar (.i64 word) :: rest) memory =
      .ok (.next target rest frame memory) := by
  rw [step_blt_zero, ite_eq_left (by exact negative)]

private theorem step_blt_nonneg {body : CIL.Method} {pc target : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {word : BitVec 64} (negative : ¬word.toInt < 0) :
    step body (.blt target) pc args frame (.scalar (.i64 0) :: .scalar (.i64 word) :: rest) memory =
      .ok (.next (pc + 1) rest frame memory) := by
  rw [step_blt_zero, ite_eq_right (by exact negative)]

set_option hygiene false in
/-- One instruction step, closed by a targeted lemma or by definitional unfolding. -/
macro "leaf_step" : tactic =>
  `(tactic| refine (run_next found rfl (by
      first
        | (with_reducible exact step_arg_first formed)
        | (with_reducible exact step_arg_second formed)
        | ((with_reducible apply step_field); first | with_reducible exact field0 _ | with_reducible exact field1 _ | with_reducible exact field2 _ | with_reducible exact field3 _)
        | ((with_reducible apply step_brnonzero_zero); with_reducible assumption)
        | ((with_reducible apply step_brnonzero_ne); with_reducible assumption)
        | (with_reducible exact step_convI8_zero)
        | ((with_reducible apply step_blt_neg); with_reducible assumption)
        | ((with_reducible apply step_blt_nonneg); with_reducible assumption)
        | rfl)).trans ?_)

set_option hygiene false in
/-- Run to the return, then discharge the small result equation. -/
macro "leaf_finish" "with" facts:term,* : tactic =>
  `(tactic| (
    repeat leaf_step
    refine (run_return found rfl rfl rfl).trans ?_
    simp [result, CIL.NarrowKind.extend, BitVec.lt_def, $[$facts:term],*]
    try (split <;> rfl)))

/-- Prove the helper once for any surrounding program and method index.
    The lookup premise binds the entire body, including profile and frame metadata. -/
theorem run_template (leafSigned leafScalarFirst : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (method leafSigned leafScalarFirst)) (memory : Memory) (input : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions program memory [input] []) :
    run program 22 index 0
      (scalarOperatorArguments leafScalarFirst input (.i64 word)) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (result leafSigned leafScalarFirst memory input word))]) := by
  have formed := call.input_formed (reference := input) (by simp)
  have fields := fun index rest => call.input_field_instruction (reference := input) (by simp) index rest
  have field0 := fields (0 : Fin 4)
  have field1 := fields (1 : Fin 4)
  have field2 := fields (2 : Fin 4)
  have field3 := fields (3 : Fin 4)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at field0 field1 field2 field3
  cases leafSigned <;> cases leafScalarFirst <;>
    simp only [method, Bool.false_eq_true, ite_true, ite_false] at found <;>
    simp only [scalarOperatorArguments, scalarArguments, Bool.false_eq_true, ite_true, ite_false]
  · by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
    · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
      · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
        · leaf_finish with h1, h2, h3
        · leaf_finish with h1, h2, h3
      · leaf_finish with h2, h3
    · leaf_finish with h3
  · by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
    · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
      · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
        · leaf_finish with h1, h2, h3
        · leaf_finish with h1, h2, h3
      · leaf_finish with h2, h3
    · leaf_finish with h3
  · by_cases negative : word.toInt < 0
    · leaf_finish with negative
    · by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
      · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
        · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
          · leaf_finish with h1, h2, h3, negative
          · leaf_finish with h1, h2, h3, negative
        · leaf_finish with h2, h3, negative
      · leaf_finish with h3, negative
  · by_cases negative : word.toInt < 0
    · leaf_finish with negative
    · by_cases h1 : inputLimb memory input 1 = BitVec.ofNat 64 0
      · by_cases h2 : inputLimb memory input 2 = BitVec.ofNat 64 0
        · by_cases h3 : inputLimb memory input 3 = BitVec.ofNat 64 0
          · leaf_finish with h1, h2, h3, negative
          · leaf_finish with h1, h2, h3, negative
        · leaf_finish with h1, h2, negative
      · leaf_finish with h1, negative

#print axioms run_template
end UInt256Proof.Compare.PrimitiveLeaf
