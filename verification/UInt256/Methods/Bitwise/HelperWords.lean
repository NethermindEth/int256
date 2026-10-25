import UInt256.Methods.Bitwise.ScalarSafetyContract
import CIL.Safety.CallComposition
import CIL.Safety.SymbolicExecution

namespace UInt256Proof.Bitwise.Helper
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise

def wordBody (profile : CIL.FeatureProfile) (operation : Binary) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], code := match operation with
    | .and => [.arg 0, .bnot, .arg 1, .bnot, .bor, .bnot, .ret]
    | .or => [.arg 0, .bnot, .arg 1, .bnot, .band, .bnot, .ret]
    | .xor => [.arg 0, .arg 1, .bor, .arg 0, .arg 1, .band, .bnot, .band, .ret] }

theorem and_identity (a b : BitVec 64) : ~~~(~~~a ||| ~~~b) = a &&& b := by
  rw [BitVec.not_or, BitVec.not_not, BitVec.not_not]
theorem or_identity (a b : BitVec 64) : ~~~(~~~a &&& ~~~b) = a ||| b := by
  rw [BitVec.not_and, BitVec.not_not, BitVec.not_not]
theorem xor_identity (a b : BitVec 64) : (a ||| b) &&& ~~~(a &&& b) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_xor, bound, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem word_checked (operation : Binary) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (wordBody profile operation))
    (memory : Memory) (a b : BitVec 64) :
    invoke program 10 index [.scalar (.i64 a), .scalar (.i64 b)] memory =
      .ok (memory, [.scalar (.i64 (wordOperation operation a b))]) := by
  cases operation
  · rw [wordOperation, ← and_identity]; cil_checked_steps
  · rw [wordOperation, ← or_identity]; cil_checked_steps
  · rw [wordOperation, ← xor_identity]; cil_checked_steps

#print axioms word_checked

theorem limb_checked (operation : Binary) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index helper pc : Nat) (body : CIL.Method)
    (found : program[index]? = some body)
    (helperFound : program[helper]? = some (wordBody profile operation))
    (limb : Fin 4)
    (h0 : body.code[pc]? = some (.arg 0))
    (h1 : body.code[pc + 1]? = some (.fieldAt (8 * limb.val) 8))
    (h2 : body.code[pc + 2]? = some (.arg 1))
    (h3 : body.code[pc + 3]? = some (.fieldAt (8 * limb.val) 8))
    (h4 : body.code[pc + 4]? = some (.call helper 2))
    (memory final : Memory) (left right output : Reference) (frame : Frame)
    (rest values : List Value)
    (call : CallingConditions program memory [left, right] [output])
    (continuation : ∃ fuel, run program fuel index (pc + 5)
      (binaryArguments left right output) frame
      (.scalar (.i64 (wordOperation operation (inputLimb memory left limb)
        (inputLimb memory right limb))) :: rest) memory = .ok (final, values)) :
    ∃ fuel, run program fuel index pc (binaryArguments left right output) frame rest memory =
      .ok (final, values) := by
  have child := word_checked operation profile program helper helperFound memory
    (inputLimb memory left limb) (inputLimb memory right limb)
  have next : ∃ fuel, run program fuel index (pc + 4)
      (binaryArguments left right output) frame
      (.scalar (.i64 (inputLimb memory right limb)) ::
       .scalar (.i64 (inputLimb memory left limb)) :: rest) memory = .ok (final, values) := by
    apply run_call_exists found h4 (by rfl) ⟨10, child⟩
    simpa only [Nat.add_assoc, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero, Nat.reduceAdd] using continuation
  obtain ⟨fuel, finished⟩ := next
  refine ⟨fuel + 4, ?_⟩
  have leftFormed := call.input_formed (reference := left) (by simp)
  have rightFormed := call.input_formed (reference := right) (by simp)
  have leftField := call.input_field_instruction (reference := left) (by simp) limb
  have rightField := call.input_field_instruction (reference := right) (by simp) limb
  cil_checked_steps 4 [found, h0, h1, h2, h3, binaryArguments,
    leftFormed, rightFormed, leftField, rightField]
  simpa only [Nat.add_assoc] using finished

#print axioms limb_checked

def binaryBody (profile : CIL.FeatureProfile) (constructor helper : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code := [
    .arg 2,
    .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .call helper 2,
    .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .call helper 2,
    .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .call helper 2,
    .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .call helper 2,
    .newAggregate constructor 4 32, .storeAggregate 32, .ret] }

theorem binary_result (operation : Binary) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index constructor helper : Nat)
    (found : program[index]? = some (binaryBody profile constructor helper))
    (constructorFound : program[constructor]? = some (UInt256Proof.ConstructorSafety.body profile))
    (helperFound : program[helper]? = some (wordBody profile operation))
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final, InvocationCertificate program index (binaryArguments left right output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (applyBinary operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset := by
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  let w := fun i => wordOperation operation (inputLimb memory left i) (inputLimb memory right i)
  obtain ⟨fuel, final, tail, readback, writable, outside⟩ :=
    ScalarSafety.construct_result program index 21 constructor (binaryBody profile constructor helper)
      profile found constructorFound (by rfl) (by rfl) (by rfl) (by rfl)
      memory [left, right] output (binaryArguments left right output) (w 0) (w 1) (w 2) (w 3) call
  have prefixRun : ∃ fuel, run program fuel index 1 (binaryArguments left right output) frame
      [.reference (.address output)] memory = .ok (final, []) := by
    apply limb_checked operation profile program index helper 1 _ found helperFound 0
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) memory final left right output frame _ [] call
    apply limb_checked operation profile program index helper 6 _ found helperFound 1
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) memory final left right output frame _ [] call
    apply limb_checked operation profile program index helper 11 _ found helperFound 2
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) memory final left right output frame _ [] call
    apply limb_checked operation profile program index helper 16 _ found helperFound 3
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) memory final left right output frame _ [] call
    exact ⟨fuel, tail⟩
  obtain ⟨prefixFuel, prefixRun⟩ := prefixRun
  have finished : run program (prefixFuel + 1) index 0 (binaryArguments left right output)
      frame [] memory = .ok (final, []) := by
    apply Eq.trans
    · apply run_next (target := 1) (values := [.reference (.address output)])
        (nextFrame := frame) (updated := memory) found (by rfl)
      cil_checked_step [binaryArguments, call.output_formed (by simp : output ∈ [output])]
    exact prefixRun
  have setup : enterFrame (binaryBody profile constructor helper) (binaryArguments left right output) memory =
      .ok (frame, memory) := rfl
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    simp [binaryArguments, checkedValue, formValue, call.input_formed (by simp : left ∈ [left, right]),
      call.input_formed (by simp : right ∈ [left, right]), call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨prefixFuel + 1, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (call.binary_entry_live setup) finished, ?_, writable, outside⟩
  change read final output 32 1 = .ok (numberBytes _ 32) at readback
  simpa only [w, packed_operation] using readback

#print axioms binary_result

theorem binary_correctness (operation : Binary) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index constructor helper : Nat)
    (found : program[index]? = some (binaryBody profile constructor helper))
    (constructorFound : program[constructor]? = some (UInt256Proof.ConstructorSafety.body profile))
    (helperFound : program[helper]? = some (wordBody profile operation)) :
    WrappingBinaryContract (applyBinary operation) program index := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, readback, writable, outside⟩ :=
    binary_result operation profile program index constructor helper found constructorFound helperFound
      memory left right output call
  refine ⟨fuel, final, certificate, ?_, writable, outside⟩
  have decoded := output_snapshot_value final output _ readback
  rw [byteNumber_numberBytes] at decoded
  simpa only [show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using decoded.symm

#print axioms binary_correctness
end UInt256Proof.Bitwise.Helper
