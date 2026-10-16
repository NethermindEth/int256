import UInt256.Methods.Bitwise.Contract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import CIL.SymbolicExecution

namespace UInt256Proof.Bitwise
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise

def opcode : Binary → CIL.Op
  | .and => .band
  | .or => .bor
  | .xor => .bxor

def wordOperation (operation : Binary) (a b : BitVec 64) : BitVec 64 :=
  match operation with
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b

/-- Keep the interpreter reduction outside the per-limb execution proof. -/
theorem word_step (operation : Binary) (body : CIL.Method) (pc : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) (a b : BitVec 64) :
    step body (opcode operation) pc args frame
      (.scalar (.i64 b) :: .scalar (.i64 a) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i64 (wordOperation operation a b)) :: rest) frame memory) := by
  cases operation <;> rfl

private theorem feature_step (body : CIL.Method) (pc : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) :
    step body (.feature .vector256Accelerated) pc args frame rest memory =
      .ok (.next (pc + 1)
        (.scalar (.i32 (if body.profile.vector256Accelerated then 1 else 0)) :: rest) frame memory) := by
  rfl

theorem scalar_branch (body : CIL.Method) (pc target : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) :
    step body (.brzero target) pc args frame (.scalar (.i32 0) :: rest) memory =
      .ok (.next target rest frame memory) := by
  rfl

theorem feature_disabled (body : CIL.Method)
    (disabled : body.profile.vector256Accelerated = false) (pc : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) :
    step body (.feature .vector256Accelerated) pc args frame rest memory =
      .ok (.next (pc + 1) (.scalar (.i32 0) :: rest) frame memory) := by
  rw [feature_step, disabled]
  rfl

def scalarBody (profile : CIL.FeatureProfile) (operation : Binary) (constructor : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code := [
    .feature .vector256Accelerated, .brzero 7,
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .arg 2,
    .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, opcode operation,
    .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, opcode operation,
    .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, opcode operation,
    .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, opcode operation,
    .newAggregate constructor 4 32, .storeAggregate 32, .ret] }

macro "bitwise_step_simp" facts:term,* : tactic =>
  `(tactic| simp [step, binaryArguments, checkedValue, numericValue, formValue,
      pureArity, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure, cil_code, $[$facts:term],*])

/-- All four input pairs are read before construction or output writes. This
    shared prefix therefore permits arbitrary overlap of inputs and output. -/
theorem scalar_prefix (operation : Binary) (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (constructor : Nat)
    (program : CIL.Program) (index fuel : Nat)
    (found : program[index]? = some (scalarBody profile operation constructor))
    (memory : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output]) :
    run program (fuel + 23) index 0 (binaryArguments left right output) frame [] memory =
    run program fuel index 28 (binaryArguments left right output) frame
      [.scalar (.i64 (wordOperation operation (inputLimb memory left 3) (inputLimb memory right 3))),
       .scalar (.i64 (wordOperation operation (inputLimb memory left 2) (inputLimb memory right 2))),
       .scalar (.i64 (wordOperation operation (inputLimb memory left 1) (inputLimb memory right 1))),
       .scalar (.i64 (wordOperation operation (inputLimb memory left 0) (inputLimb memory right 0))),
       .reference (.address output)] memory := by
  have leftFormed := call.input_formed (reference := left) (by simp)
  have rightFormed := call.input_formed (reference := right) (by simp)
  have outputFormed := call.output_formed (reference := output) (by simp)
  have leftFields := fun i rest => call.input_field_instruction (reference := left) (by simp) i rest
  have rightFields := fun i rest => call.input_field_instruction (reference := right) (by simp) i rest
  have l0 := leftFields (0 : Fin 4)
  have l1 := leftFields (1 : Fin 4)
  have l2 := leftFields (2 : Fin 4)
  have l3 := leftFields (3 : Fin 4)
  have r0 := rightFields (0 : Fin 4)
  have r1 := rightFields (1 : Fin 4)
  have r2 := rightFields (2 : Fin 4)
  have r3 := rightFields (3 : Fin 4)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at l0 l1 l2 l3 r0 r1 r2 r3
  iterate 23
    apply Eq.trans
    · apply run_next found
      · simp only [scalarBody]; rfl
      · first
        | exact word_step operation _ _ _ _ _ _ _ _
        | exact feature_disabled _ scalar _ _ _ _ _
        | exact scalar_branch _ _ _ _ _ _ _
        | (bitwise_step_simp leftFormed, rightFormed, outputFormed, l0, l1, l2, l3, r0, r1, r2, r3
           try exact ⟨rfl, rfl, rfl, rfl⟩
           done)
  rfl

#print axioms word_step
#print axioms scalar_prefix
end UInt256Proof.Bitwise
