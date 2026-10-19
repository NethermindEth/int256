import Extracted
import UInt256.Methods.Bindings
import UInt256.Methods.Equality.ReferenceOperator
import UInt256.Methods.Equality.PrimitiveOperator
import UInt256.Methods.ValueForwarder32
import UInt256.Methods.Equality.SignedPrimitive
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyScalarExecution
import CIL.SymbolicExecution


namespace EqualityFixture.LeafVectorPrimitive
open UInt256Proof UInt256Proof.Equality
open CIL.Safety UInt256Model.Safety

def inputBytes (memory : Memory) (input : Reference) : List (BitVec 8) :=
  (List.range 32).map fun i => (memory.cells input.allocation (input.offset + i)).bits

theorem load_input {program : CIL.Program} {memory : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {input : Reference} (member : input ∈ inputs)
    (rest : List Value) :
    instruction (.loadAggregate 32) (.reference (.address input) :: rest) memory =
      .ok (memory, .scalar (.aggregate (inputBytes memory input)) :: rest) := by
  have loaded := call.input_snapshot member
  simp [instruction, dereference, ordinaryAccessAlignment, loaded, inputBytes, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem cast_input (memory : Memory) (input : Reference) (rest : List Value) :
    memoryInstruction (.bitcastValue (.aggregate 32) .vector256)
      (.scalar (.aggregate (inputBytes memory input)) :: rest) memory =
      .ok (memory, .scalar (.v256 (inputValue memory input)) :: rest) := by
  simp [memoryInstruction, bitcastValue, valueSnapshot, snapshotValue, CIL.SnapshotShape.width,
    inputBytes, List.map_map, Function.comp_def, byteNumber_snapshot, inputValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

  rw [byteNumber_snapshot (fun offset => (memory.cells input.allocation offset).bits) input.offset 32]
  rfl

def body (narrow : Bool) (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], code := [
    .arg 1, .intrinsic (.vector (if narrow then .createScalar32 256 else .createScalar64 256)) 1,
    .arg 0, .loadAggregate 32, .memory (.bitcastValue (.aggregate 32) .vector256),
    .intrinsic (.vector (.equalsAll 256)) 2, .ret (some .unsigned8)] }

theorem eval_scalar32 (word : BitVec 32) :
    CIL.evalIntrinsic (.vector (.createScalar32 256)) [.i32 word] = some (.v256 (word.zeroExtend 256)) := rfl
theorem eval_scalar64 (word : BitVec 64) :
    CIL.evalIntrinsic (.vector (.createScalar64 256)) [.i64 word] = some (.v256 (word.zeroExtend 256)) := rfl
theorem eval_xor (a b : BitVec 256) :
    CIL.evalIntrinsic (.vector (.bxor 256)) [.v256 a, .v256 b] = some (.v256 (a ^^^ b)) := rfl
theorem eval_zero : CIL.evalIntrinsic (.vector (.zero 256)) [] = some (.v256 0) := rfl
theorem eval_equal (a b : BitVec 256) :
    CIL.evalIntrinsic (.vector (.equalsAll 256)) [.v256 a, .v256 b] =
      some (.i32 (if a = b then 1 else 0)) := by
  change some (CIL.Value.i32 (if a == b then 1 else 0)) = _
  simp

theorem run64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body false profile))
    (memory : Memory) (left : Reference) (right : BitVec 64) (frame : Frame)
    (call : CallingConditions program memory [left] []) :
    ∃ fuel, run program fuel index 0 (scalarArguments left (.i64 right)) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = right.zeroExtend 256 then 1 else 0))]) := by
  have formed := call.input_formed (reference := left) (by simp)
  have loaded := load_input call (input := left) (by simp)
  have casted := cast_input memory left
  generalize valueEq : inputValue memory left = value at *
  refine ⟨8, ?_⟩
  iterate 6
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [body, step, scalarArguments, checkedValue, numericValue, formValue, formed,
            loaded, casted, staticInstruction, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
            eval_scalar32, eval_scalar64, eval_xor, eval_zero, eval_equal,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl, rfl, rfl, rfl⟩
        done
  simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  split <;> rename_i h <;> simp [h, eq_comm]
  exact Ne.symm h

#print axioms run64
theorem run32 (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body true profile))
    (memory : Memory) (left : Reference) (right : BitVec 32) (frame : Frame)
    (call : CallingConditions program memory [left] []) :
    ∃ fuel, run program fuel index 0 (scalarArguments left (.i32 right)) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = right.zeroExtend 256 then 1 else 0))]) := by
  have formed := call.input_formed (reference := left) (by simp)
  have loaded := load_input call (input := left) (by simp)
  have casted := cast_input memory left
  generalize valueEq : inputValue memory left = value at *
  refine ⟨8, ?_⟩
  iterate 6
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [body, step, scalarArguments, checkedValue, numericValue, formValue, formed,
            loaded, casted, staticInstruction, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
            eval_scalar32, eval_scalar64, eval_xor, eval_zero, eval_equal,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl, rfl, rfl, rfl⟩
        done
  simp [run, found, body, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  split <;> rename_i h <;> simp [h, eq_comm]
  exact Ne.symm h


#print axioms run32













theorem checked32 (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body true profile)) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun input word => .i32 (if input = word.zeroExtend 256 then 1 else 0)) program index :=
  certify_readOnly_scalar program index (body true profile) CIL.Value.i32 _ found (fun _ => rfl)
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit])
    (run32 profile program index found)

#print axioms checked32
theorem checked64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body false profile)) :
    ReadOnlyScalarContract CIL.Value.i64
      (fun input word => .i32 (if input = word.zeroExtend 256 then 1 else 0)) program index :=
  certify_readOnly_scalar program index (body false profile) CIL.Value.i64 _ found (fun _ => rfl)
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit])
    (run64 profile program index found)

#print axioms checked64
end EqualityFixture.LeafVectorPrimitive


namespace EqualityFixture.LeafPrimitiveWrapper
open UInt256Proof UInt256Proof.Equality
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
    (leafFound : program[callee]? = some (EqualityFixture.LeafVectorPrimitive.body narrow profile))
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
    (leafFound : program[callee]? = some (EqualityFixture.LeafVectorPrimitive.body narrow profile))
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
    (leafFound : program[callee]? = some (EqualityFixture.LeafVectorPrimitive.body true profile)) :
    ScalarOperatorContract false false CIL.Value.i32
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  have widen (word : BitVec 32) : word.zeroExtend 256 = BitVec.ofNat 256 word.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply checked CIL.Value.i32 _ true profile program index callee vector found leafFound (fun _ => rfl)
  intro memory left right frame call
  simpa only [decide_eq_true_eq, widen] using EqualityFixture.LeafVectorPrimitive.run32 profile program callee leafFound memory left right frame call

#print axioms checked32
theorem checked64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body false profile callee))
    (leafFound : program[callee]? = some (EqualityFixture.LeafVectorPrimitive.body false profile)) :
    ScalarOperatorContract false false CIL.Value.i64
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  have widen (word : BitVec 64) : word.zeroExtend 256 = BitVec.ofNat 256 word.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply checked CIL.Value.i64 _ false profile program index callee vector found leafFound (fun _ => rfl)
  intro memory left right frame call
  simpa only [decide_eq_true_eq, widen] using EqualityFixture.LeafVectorPrimitive.run64 profile program callee leafFound memory left right frame call

#print axioms checked64
end EqualityFixture.LeafPrimitiveWrapper

/-- EquivalentReduction fixture for EqInt32UInt256 on x64-vector256, stated with the production contract. -/
theorem EqualityFixture.correct :
    UInt256Model.Safety.ScalarOperatorContract true false CIL.Value.i32 (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) Extracted.program 0 :=
  UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i32 _ Extracted.profile true false Extracted.program 0 1 rfl (fun _ => rfl)
    (UInt256Proof.Equality.SignedPrimitive.checked32 Extracted.profile Extracted.program 1 2 rfl
    (EqualityFixture.LeafPrimitiveWrapper.checked32 Extracted.profile Extracted.program 2 3 rfl rfl rfl))

#print axioms EqualityFixture.correct
