import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyScalarExecution
import CIL.SymbolicExecution
import UInt256.Safety.StepEquation

namespace UInt256Proof.Equality.VectorPrimitive
open CIL.Safety UInt256Model.Safety

def inputBytes (memory : Memory) (input : Reference) : List (BitVec 8) :=
  (List.range 32).map fun i => (memory.cells input.allocation (input.offset + i)).bits

theorem load_input {program : CIL.Program} {memory : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {input : Reference} (member : input ∈ inputs)
    (rest : List Value) :
    instruction (.loadAggregate 32) (.reference (.address input) :: rest) memory =
      .ok (memory, .scalar (.aggregate (inputBytes memory input)) :: rest) := by
  have loaded := call.input_snapshot member
  unfold instruction
  simp only [dereference, ordinaryAccessAlignment, loaded, inputBytes, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem cast_input (memory : Memory) (input : Reference) (rest : List Value) :
    memoryInstruction (.bitcastValue (.aggregate 32) .vector256)
      (.scalar (.aggregate (inputBytes memory input)) :: rest) memory =
      .ok (memory, .scalar (.v256 (inputValue memory input)) :: rest) := by
  have value : inputValue memory input = BitVec.ofNat 256 (byteNumber (inputBytes memory input)) := by
    rw [inputBytes, byteNumber_snapshot (fun offset => (memory.cells input.allocation offset).bits) input.offset 32]
    rfl
  rw [value]
  rfl

private theorem s_arg {body : CIL.Method} {pc i : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {m : Memory} {r : Reference}
    (h : args[i]? = some (.reference (.address r))) (formed : form m r = .ok r) :
    step body (.arg i) pc args frame stack m = .ok (.next (pc + 1) (.reference (.address r) :: stack) frame m) := by
  unfold step
  simp only [h, checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

private theorem s_loadAggregate {body : CIL.Method} {pc size : Nat} {args : List Value} {frame : Frame}
    {stack values : List Value} {m m' : Memory}
    (h : instruction (.loadAggregate size) stack m = .ok (m', values)) :
    step body (.loadAggregate size) pc args frame stack m = .ok (.next (pc + 1) values frame m') := by
  unfold step
  simp only [show pureArity (.loadAggregate size) = none from rfl, h, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

private theorem s_bitcast {body : CIL.Method} {pc : Nat} {args : List Value} {frame : Frame}
    {stack values : List Value} {m m' : Memory} {source target : CIL.SnapshotShape}
    (h : memoryInstruction (.bitcastValue source target) stack m = .ok (m', values)) :
    step body (.memory (.bitcastValue source target)) pc args frame stack m =
      .ok (.next (pc + 1) values frame m') := by
  unfold step staticInstruction
  simp only [h, Bind.bind, Except.bind, Pure.pure, Except.pure]

def body (narrow : Bool) (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], code := [
    .arg 1, .intrinsic (.vector (if narrow then .createScalar32 256 else .createScalar64 256)) 1,
    .arg 0, .loadAggregate 32, .memory (.bitcastValue (.aggregate 32) .vector256),
    .intrinsic (.vector (.bxor 256)) 2, .intrinsic (.vector (.zero 256)) 0,
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
  refine ⟨10, ?_⟩
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (s_arg (by rfl) formed)).trans ?_
  refine (run_next found rfl (s_loadAggregate (loaded _))).trans ?_
  refine (run_next found rfl (s_bitcast (casted _))).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_return found rfl rfl rfl).trans ?_
  simp [leaveFrame, CIL.NarrowKind.extend]
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
  refine ⟨10, ?_⟩
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (s_arg (by rfl) formed)).trans ?_
  refine (run_next found rfl (s_loadAggregate (loaded _))).trans ?_
  refine (run_next found rfl (s_bitcast (casted _))).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_next found rfl (rfl)).trans ?_
  refine (run_return found rfl rfl rfl).trans ?_
  simp [leaveFrame, CIL.NarrowKind.extend]
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
end UInt256Proof.Equality.VectorPrimitive
