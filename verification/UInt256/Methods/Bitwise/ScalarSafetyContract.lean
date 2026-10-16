import UInt256.Methods.Bitwise.ScalarPrefix
import UInt256.Methods.Bitwise.ScalarSafetyConstruct
import UInt256.Methods.Bitwise.Lemmas
import UInt256.Safety.Contract

namespace UInt256Proof.Bitwise
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise UInt256Proof.ConstructorSafety

theorem packed_operation (operation : Binary) (memory : Memory) (left right : Reference) :
    packed
      (wordOperation operation (inputLimb memory left 0) (inputLimb memory right 0))
      (wordOperation operation (inputLimb memory left 1) (inputLimb memory right 1))
      (wordOperation operation (inputLimb memory left 2) (inputLimb memory right 2))
      (wordOperation operation (inputLimb memory left 3) (inputLimb memory right 3)) =
      applyBinary operation (inputValue memory left) (inputValue memory right) := by
  have lv : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value _ _
  have rv : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value _ _
  change UInt256Model.value (fun i => wordOperation operation (inputLimb memory left i) (inputLimb memory right i)) = _
  cases operation <;> simp only [wordOperation, applyBinary, value_and, value_or, value_xor, lv, rv]

theorem scalar_result (operation : Binary) (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (program : CIL.Program) (index constructor : Nat)
    (found : program[index]? = some (scalarBody profile operation constructor))
    (constructorFound : program[constructor]? = some (body profile)) :
    ∀ memory left right output, CallingConditions program memory [left, right] [output] →
    ∃ fuel final, InvocationCertificate program index (binaryArguments left right output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (applyBinary operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset := by
  intro memory left right output call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  obtain ⟨fuel, final, tail, readback, writable, outside⟩ :=
    ScalarSafety.construct_result program index 28 constructor (scalarBody profile operation constructor)
      profile found constructorFound (by rfl) (by rfl) (by rfl) (by rfl)
      memory [left, right] output (binaryArguments left right output)
      (wordOperation operation (inputLimb memory left 0) (inputLimb memory right 0))
      (wordOperation operation (inputLimb memory left 1) (inputLimb memory right 1))
      (wordOperation operation (inputLimb memory left 2) (inputLimb memory right 2))
      (wordOperation operation (inputLimb memory left 3) (inputLimb memory right 3)) call
  have finished := (scalar_prefix operation profile scalar constructor program index fuel found
    memory left right output frame call).trans tail
  have setup : enterFrame (scalarBody profile operation constructor) (binaryArguments left right output) memory =
      .ok (frame, memory) := rfl
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    simp [binaryArguments, checkedValue, formValue, call.input_formed (by simp : left ∈ [left, right]),
      call.input_formed (by simp : right ∈ [left, right]), call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel + 23, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (call.binary_entry_live setup) finished, ?_, writable, outside⟩
  rw [packed_operation] at readback
  exact readback

theorem scalar_correctness (operation : Binary) (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (program : CIL.Program) (index constructor : Nat)
    (found : program[index]? = some (scalarBody profile operation constructor))
    (constructorFound : program[constructor]? = some (body profile)) :
    WrappingBinaryContract (applyBinary operation) program index := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, readback, writable, outside⟩ :=
    scalar_result operation profile scalar program index constructor found constructorFound memory left right output call
  refine ⟨fuel, final, certificate, ?_, writable, outside⟩
  have decoded := output_snapshot_value final output _ readback
  rw [byteNumber_numberBytes] at decoded
  simpa only [show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using decoded.symm

#print axioms scalar_correctness
#print axioms packed_operation
#print axioms scalar_result
end UInt256Proof.Bitwise
