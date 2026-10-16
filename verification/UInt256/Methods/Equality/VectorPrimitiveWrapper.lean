import UInt256.Methods.Equality.VectorPrimitive
import UInt256.Methods.Equality.PrimitiveOperator

namespace UInt256Proof.Equality.VectorPrimitiveWrapper
open CIL.Safety UInt256Model.Safety

def body32 (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 16,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8)] }

def body64 (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 15,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8)] }

def body (narrow : Bool) (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  if narrow then body32 profile callee else body64 profile callee

def callPC (narrow : Bool) : Nat := if narrow then 18 else 17

theorem executed {α : Type} (encode : α → CIL.Value) (equal : BitVec 256 → α → Bool)
    (narrow : Bool) (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body narrow profile callee))
    (leafFound : program[callee]? = some (VectorPrimitive.body narrow profile))
    (numeric : ∀ word, numericValue (encode word) = true)
    (childRun : ∀ memory left right frame, CallingConditions program memory [left] [] →
      ∃ fuel, run program fuel callee 0 (scalarArguments left (encode right)) frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (if equal (inputValue memory left) right then 1 else 0))]))
    (memory : Memory) (left : Reference) (right : α) (frame : Frame)
    (call : CallingConditions program memory [left] []) :
    ∃ fuel, run program fuel index 0 (scalarArguments left (encode right)) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if equal (inputValue memory left) right then 1 else 0))]) := by
  let childFrame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have formed := call.input_formed (reference := left) (by simp)
  have numericWord := numeric right
  simp only [numericValue] at numericWord
  obtain ⟨childFuel, childExecution⟩ := childRun memory left right childFrame call
  have child : invoke program childFuel callee (scalarArguments left (encode right)) memory =
      .ok (memory, [.scalar (.i32 (if equal (inputValue memory left) right then 1 else 0))]) := by
    apply invoke_of_run leafFound
    · simp [scalarArguments, checkedValue, numeric, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rfl
    · simpa [leaveFrame, childFrame] using childExecution
  have returnTrace : run program 1 index (callPC narrow + 1) (scalarArguments left (encode right)) frame
      [.scalar (.i32 (if equal (inputValue memory left) right then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if equal (inputValue memory left) right then 1 else 0))]) := by
    cases narrow <;> cases equal (inputValue memory left) right <;>
      simp [run, found, body, body32, body64, callPC, step, checkedValue, numericValue, CIL.NarrowKind.extend,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have fetched : (body narrow profile callee).code[callPC narrow]? = some (.call callee 2) := by
    cases narrow <;> rfl
  have stepped : step (body narrow profile callee) (.call callee 2) (callPC narrow)
      (scalarArguments left (encode right)) frame [.scalar (encode right), .reference (.address left)] memory =
      .ok (.call callee (scalarArguments left (encode right)) [] memory) := by
    simp [step, scalarArguments, checkedValue, numeric, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, child⟩ ⟨1, returnTrace⟩
  refine ⟨fuel + 4, ?_⟩
  cases narrow
  all_goals
    iterate 4
      apply Eq.trans
      · apply run_next found
        · simp only [body, body32, body64]; rfl
        · simp (config := { implicitDefEqProofs := false }) [body, body32, body64, step, scalarArguments,
            checkedValue, numericValue, numeric, numericWord, formValue, formed, pureArity, scalars, CIL.step.eq_def, CIL.truth,
            CIL.FeatureProfile.evaluate, vector, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try exact ⟨rfl, rfl, rfl, rfl⟩
    exact tail

theorem checked {α : Type} (encode : α → CIL.Value) (equal : BitVec 256 → α → Bool)
    (narrow : Bool) (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body narrow profile callee))
    (leafFound : program[callee]? = some (VectorPrimitive.body narrow profile))
    (numeric : ∀ word, numericValue (encode word) = true)
    (childRun : ∀ memory left right frame, CallingConditions program memory [left] [] →
      ∃ fuel, run program fuel callee 0 (scalarArguments left (encode right)) frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (if equal (inputValue memory left) right then 1 else 0))])) :
    ScalarOperatorContract false false encode equal program index := by
  have result := certify_readOnly_scalar program index (body narrow profile callee) encode
    (fun input word => .i32 (if equal input word then 1 else 0)) found numeric
    (by intro left right; cases narrow <;>
        (simp [body, body32, body64, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit]; rfl))
    (executed encode equal narrow profile program index callee vector found leafFound numeric childRun)
  simpa only [ScalarOperatorContract, ReadOnlyScalarContract, scalarOperatorArguments,
    Bool.false_eq_true, ite_false, Bool.bne_false] using result

#print axioms executed
#print axioms checked






theorem checked32 (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body true profile callee))
    (leafFound : program[callee]? = some (VectorPrimitive.body true profile)) :
    ScalarOperatorContract false false CIL.Value.i32
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  have widen (word : BitVec 32) : word.zeroExtend 256 = BitVec.ofNat 256 word.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply checked CIL.Value.i32 _ true profile program index callee vector found leafFound (fun _ => rfl)
  intro memory left right frame call
  simpa only [decide_eq_true_eq, widen] using VectorPrimitive.run32 profile program callee leafFound memory left right frame call

#print axioms checked32
theorem checked64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body false profile callee))
    (leafFound : program[callee]? = some (VectorPrimitive.body false profile)) :
    ScalarOperatorContract false false CIL.Value.i64
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  have widen (word : BitVec 64) : word.zeroExtend 256 = BitVec.ofNat 256 word.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply checked CIL.Value.i64 _ false profile program index callee vector found leafFound (fun _ => rfl)
  intro memory left right frame call
  simpa only [decide_eq_true_eq, widen] using VectorPrimitive.run64 profile program callee leafFound memory left right frame call

#print axioms checked64
end UInt256Proof.Equality.VectorPrimitiveWrapper
