import UInt256.Methods.Bitwise.NotScalar
import CIL.Safety.CallComposition

namespace UInt256Proof.Bitwise.Helper
open CIL.Safety UInt256Model.Safety

def notWordBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], code :=
    [.arg 0, .const32 (BitVec.ofInt 32 (-1)), .convI8, .bxor, .ret] }

theorem not_word_checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (notWordBody profile)) (memory : Memory) (a : BitVec 64) :
    invoke program 6 index [.scalar (.i64 a)] memory = .ok (memory, [.scalar (.i64 (~~~a))]) := by
  rw [← BitVec.xor_allOnes]
  cil_checked_steps

theorem not_limb_checked (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index helper pc : Nat) (body : CIL.Method)
    (found : program[index]? = some body)
    (helperFound : program[helper]? = some (notWordBody profile))
    (limb : Fin 4)
    (h0 : body.code[pc]? = some (.arg 0))
    (h1 : body.code[pc + 1]? = some (.fieldAt (8 * limb.val) 8))
    (h2 : body.code[pc + 2]? = some (.call helper 1))
    (memory final : Memory) (input output : Reference) (frame : Frame)
    (rest values : List Value)
    (call : CallingConditions program memory [input] [output])
    (continuation : ∃ fuel, run program fuel index (pc + 3) (unaryArguments input output) frame
      (.scalar (.i64 (~~~inputLimb memory input limb)) :: rest) memory = .ok (final, values)) :
    ∃ fuel, run program fuel index pc (unaryArguments input output) frame rest memory =
      .ok (final, values) := by
  have child := not_word_checked profile program helper helperFound memory (inputLimb memory input limb)
  have next : ∃ fuel, run program fuel index (pc + 2) (unaryArguments input output) frame
      (.scalar (.i64 (inputLimb memory input limb)) :: rest) memory = .ok (final, values) := by
    apply run_call_exists found h2 (by rfl) ⟨6, child⟩
    simpa only [Nat.add_assoc, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_zero, Nat.reduceAdd] using continuation
  obtain ⟨fuel, finished⟩ := next
  refine ⟨fuel + 2, ?_⟩
  have inputFormed := call.input_formed (reference := input) (by simp)
  have inputField := call.input_field_instruction (reference := input) (by simp) limb
  cil_checked_steps 2 [found, h0, h1, unaryArguments, inputFormed, inputField]
  exact finished

def unaryBody (profile : CIL.FeatureProfile) (constructor helper : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code := [
    .arg 1,
    .arg 0, .fieldAt 0 8, .call helper 1,
    .arg 0, .fieldAt 8 8, .call helper 1,
    .arg 0, .fieldAt 16 8, .call helper 1,
    .arg 0, .fieldAt 24 8, .call helper 1,
    .newAggregate constructor 4 32, .storeAggregate 32, .ret] }

theorem unary_result (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index constructor helper : Nat)
    (found : program[index]? = some (unaryBody profile constructor helper))
    (constructorFound : program[constructor]? = some (UInt256Proof.ConstructorSafety.body profile))
    (helperFound : program[helper]? = some (notWordBody profile))
    (memory : Memory) (input output : Reference)
    (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final, InvocationCertificate program index (unaryArguments input output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (~~~inputValue memory input).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset := by
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  obtain ⟨fuel, final, tail, readback, writable, outside⟩ :=
    ScalarSafety.construct_result program index 13 constructor (unaryBody profile constructor helper)
      profile found constructorFound (by rfl) (by rfl) (by rfl) (by rfl)
      memory [input] output (unaryArguments input output)
      (~~~inputLimb memory input 0) (~~~inputLimb memory input 1)
      (~~~inputLimb memory input 2) (~~~inputLimb memory input 3) call
  have prefixRun : ∃ fuel, run program fuel index 1 (unaryArguments input output) frame
      [.reference (.address output)] memory = .ok (final, []) := by
    apply not_limb_checked profile program index helper 1 _ found helperFound 0
      (by rfl) (by rfl) (by rfl) memory final input output frame _ [] call
    apply not_limb_checked profile program index helper 4 _ found helperFound 1
      (by rfl) (by rfl) (by rfl) memory final input output frame _ [] call
    apply not_limb_checked profile program index helper 7 _ found helperFound 2
      (by rfl) (by rfl) (by rfl) memory final input output frame _ [] call
    apply not_limb_checked profile program index helper 10 _ found helperFound 3
      (by rfl) (by rfl) (by rfl) memory final input output frame _ [] call
    exact ⟨fuel, tail⟩
  obtain ⟨prefixFuel, prefixRun⟩ := prefixRun
  have finished : run program (prefixFuel + 1) index 0 (unaryArguments input output)
      frame [] memory = .ok (final, []) := by
    apply Eq.trans
    · apply run_next (target := 1) (values := [.reference (.address output)])
        (nextFrame := frame) (updated := memory) found (by rfl)
      simp [step, cil_guard, observerCount, unaryArguments, checkedValue, formValue, call.output_formed (by simp : output ∈ [output]),
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact prefixRun
  have setup : enterFrame (unaryBody profile constructor helper) (unaryArguments input output) memory =
      .ok (frame, memory) := rfl
  have checked : (unaryArguments input output).mapM (checkedValue memory) =
      .ok (unaryArguments input output) := by
    simp [unaryArguments, checkedValue, formValue, call.input_formed (by simp : input ∈ [input]),
      call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨prefixFuel + 1, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished,
    ?_, writable, outside⟩
  have value : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value _ _
  have packedNot : UInt256Proof.ConstructorSafety.packed (~~~inputLimb memory input 0) (~~~inputLimb memory input 1)
      (~~~inputLimb memory input 2) (~~~inputLimb memory input 3) = ~~~inputValue memory input := by
    change UInt256Model.value (fun i => ~~~inputLimb memory input i) = _
    rw [value_not, value]
  rw [packedNot] at readback
  exact readback

#print axioms not_word_checked
#print axioms not_limb_checked
#print axioms unary_result

theorem unary_correctness (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index constructor helper : Nat)
    (found : program[index]? = some (unaryBody profile constructor helper))
    (constructorFound : program[constructor]? = some (UInt256Proof.ConstructorSafety.body profile))
    (helperFound : program[helper]? = some (notWordBody profile)) :
    WrappingUnaryContract (~~~·) program index := by
  intro memory input output call
  obtain ⟨fuel, final, certificate, readback, writable, outside⟩ :=
    unary_result profile program index constructor helper found constructorFound helperFound memory input output call
  refine ⟨fuel, final, certificate, ?_, writable, outside⟩
  have decoded := output_snapshot_value final output _ readback
  rw [byteNumber_numberBytes] at decoded
  simpa only [show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using decoded.symm

#print axioms unary_correctness
end UInt256Proof.Bitwise.Helper
