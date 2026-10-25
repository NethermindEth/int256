import UInt256.Methods.Bitwise.ScalarSafetyContract
import UInt256.Safety.UnaryContract
import CIL.Safety.SymbolicExecution

namespace UInt256Proof.Bitwise
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

def notBody (profile : CIL.FeatureProfile) (constructor : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code := [
    .feature .vector256Accelerated, .brzero 6,
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .arg 1,
    .arg 0, .fieldAt 0 8, .bnot,
    .arg 0, .fieldAt 8 8, .bnot,
    .arg 0, .fieldAt 16 8, .bnot,
    .arg 0, .fieldAt 24 8, .bnot,
    .newAggregate constructor 4 32, .storeAggregate 32, .ret] }

theorem not_prefix (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (constructor : Nat)
    (program : CIL.Program) (index fuel : Nat)
    (found : program[index]? = some (notBody profile constructor))
    (memory : Memory) (input output : Reference) (frame : Frame)
    (call : CallingConditions program memory [input] [output]) :
    run program (fuel + 15) index 0 (unaryArguments input output) frame [] memory =
    run program fuel index 19 (unaryArguments input output) frame
      [.scalar (.i64 (~~~inputLimb memory input 3)),
       .scalar (.i64 (~~~inputLimb memory input 2)),
       .scalar (.i64 (~~~inputLimb memory input 1)),
       .scalar (.i64 (~~~inputLimb memory input 0)),
       .reference (.address output)] memory := by
  have inputFormed := call.input_formed (reference := input) (by simp)
  have outputFormed := call.output_formed (reference := output) (by simp)
  have fields := fun i rest => call.input_field_instruction (reference := input) (by simp) i rest
  have evaluated : profile.evaluate .vector256Accelerated = false := scalar
  cil_checked_steps 15 [notBody, unaryArguments, inputFormed, outputFormed, fields, evaluated]

theorem not_result (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (program : CIL.Program) (index constructor : Nat)
    (found : program[index]? = some (notBody profile constructor))
    (constructorFound : program[constructor]? = some (body profile)) :
    ∀ memory input output, CallingConditions program memory [input] [output] →
    ∃ fuel final, InvocationCertificate program index (unaryArguments input output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (~~~inputValue memory input).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset := by
  intro memory input output call
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  obtain ⟨fuel, final, tail, readback, writable, outside⟩ :=
    ScalarSafety.construct_result program index 19 constructor (notBody profile constructor)
      profile found constructorFound (by rfl) (by rfl) (by rfl) (by rfl)
      memory [input] output (unaryArguments input output)
      (~~~inputLimb memory input 0) (~~~inputLimb memory input 1)
      (~~~inputLimb memory input 2) (~~~inputLimb memory input 3) call
  have finished := (not_prefix profile scalar constructor program index fuel found
    memory input output frame call).trans tail
  have setup : enterFrame (notBody profile constructor) (unaryArguments input output) memory =
      .ok (frame, memory) := rfl
  have checked : (unaryArguments input output).mapM (checkedValue memory) =
      .ok (unaryArguments input output) := by
    simp [unaryArguments, checkedValue, formValue, call.input_formed (by simp : input ∈ [input]),
      call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨fuel + 15, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    ?_, writable, outside⟩
  have value : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value _ _
  have packedNot : packed (~~~inputLimb memory input 0) (~~~inputLimb memory input 1)
      (~~~inputLimb memory input 2) (~~~inputLimb memory input 3) = ~~~inputValue memory input := by
    change UInt256Model.value (fun i => ~~~inputLimb memory input i) = _
    rw [value_not, value]
  rw [packedNot] at readback
  exact readback

theorem not_correctness (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (program : CIL.Program) (index constructor : Nat)
    (found : program[index]? = some (notBody profile constructor))
    (constructorFound : program[constructor]? = some (body profile)) :
    WrappingUnaryContract (~~~·) program index := by
  intro memory input output call
  obtain ⟨fuel, final, certificate, readback, writable, outside⟩ :=
    not_result profile scalar program index constructor found constructorFound memory input output call
  refine ⟨fuel, final, certificate, ?_, writable, outside⟩
  have decoded := output_snapshot_value final output _ readback
  rw [byteNumber_numberBytes] at decoded
  simpa only [show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using decoded.symm

#print axioms not_result
#print axioms not_prefix
#print axioms not_correctness
end UInt256Proof.Bitwise
