import UInt256.Methods.Bitwise.EarlyStoreMemory
import UInt256.Safety.UnaryContract
import CIL.Safety.CallComposition
namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety

def unaryWordBody (profile : CIL.FeatureProfile) : CIL.Method :=
  {profile, returnsValue := true, locals := [], code := [.arg 0, .bnot, .ret]}

theorem unary_word (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (unaryWordBody profile)) (memory : Memory) (word : BitVec 64) :
    invoke program 3 index [.scalar (.i64 word)] memory = .ok (memory, [.scalar (.i64 (~~~word))]) := by
  simp only [invoke, found]
  change run program 3 index 0 [.scalar (.i64 word)] ⟨memory.nextIdentity, [], [], []⟩ [] memory = _
  iterate 2
    apply Eq.trans
    · apply run_next found (by rfl) (by rfl)
  rw [run]
  simp only [found]
  rfl

def UnaryStep (program : CIL.Program) (instruction : CIL.Op) : Prop :=
  ∀ index pc body, program[index]? = some body → body.code[pc]? = some instruction →
    ∀ memory frame args rest word final values,
      (∃ fuel, run program fuel index (pc + 1) args frame (.scalar (.i64 (~~~word)) :: rest) memory = .ok (final, values)) →
      ∃ fuel, run program fuel index pc args frame (.scalar (.i64 word) :: rest) memory = .ok (final, values)

theorem helper_unary (profile : CIL.FeatureProfile) (program : CIL.Program) (helper : Nat)
    (foundHelper : program[helper]? = some (unaryWordBody profile)) : UnaryStep program (.call helper 1) := by
  intro index pc body found fetched memory frame args rest word final values continuation
  apply run_call_exists found fetched (by rfl) ⟨3, unary_word profile program helper foundHelper memory word⟩
  simpa using continuation

theorem inline_unary (program : CIL.Program) : UnaryStep program .bnot := by
  intro index pc body found fetched memory frame args rest word final values continuation
  obtain ⟨fuel, finished⟩ := continuation
  exact ⟨fuel + 1, (run_next found fetched (by rfl)).trans finished⟩

def unaryBody (profile : CIL.FeatureProfile) (instruction : CIL.Op) (constructor : Nat) : CIL.Method :=
  {profile, returnsValue := false, locals := [], code := [
    .arg 1, .arg 0, .fieldAt 0 8, instruction,
    .const32 0, .convI8, .const32 0, .convI8, .const32 0, .convI8,
    .newAggregate constructor 4 32, .storeAggregate 32,
    .arg 1, .fieldAddress 8, .memory .asRef, .arg 0, .fieldAt 8 8, instruction, .store64,
    .arg 1, .fieldAddress 16, .memory .asRef, .arg 0, .fieldAt 16 8, instruction, .store64,
    .arg 1, .fieldAddress 24, .memory .asRef, .arg 0, .fieldAt 24 8, instruction, .store64,
    .ret]}

theorem unary_limb (program : CIL.Program) (instruction : CIL.Op) (operationStep : UnaryStep program instruction) (index pc : Nat) (body : CIL.Method)
    (found : program[index]? = some body) (limb : Fin 4)
    (h0 : body.code[pc]? = some (.arg 0))
    (h1 : body.code[pc + 1]? = some (.fieldAt (8 * limb.val) 8))
    (h2 : body.code[pc + 2]? = some instruction)
    (memory : Memory) (input output : Reference) (frame : Frame) (rest : List Value)
    (call : CallingConditions program memory [input] [output]) (final : Memory) (values : List Value)
    (continuation : ∃ fuel, run program fuel index (pc + 3) (unaryArguments input output) frame
      (.scalar (.i64 (~~~inputLimb memory input limb)) :: rest) memory = .ok (final, values)) :
    ∃ fuel, run program fuel index pc (unaryArguments input output) frame rest memory = .ok (final, values) := by
  obtain ⟨fuel, finished⟩ := operationStep index (pc + 2) body found h2 memory frame (unaryArguments input output) rest
    (inputLimb memory input limb) final values (by simpa [Nat.add_assoc] using continuation)
  refine ⟨fuel + 2, ?_⟩
  have formed := call.input_formed (by simp : input ∈ [input])
  have field := call.input_field_instruction (by simp : input ∈ [input]) limb
  apply Eq.trans
  · apply run_next (target := pc + 1) (values := .reference (.address input) :: rest) (updated := memory) (nextFrame := frame) found h0
    simp [step, unaryArguments, checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Eq.trans
  · apply run_next (target := pc + 2) (values := .scalar (.i64 (inputLimb memory input limb)) :: rest) (updated := memory) (nextFrame := frame) found h1
    simp [step, pureArity, field, Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.add_assoc]
  exact finished

theorem unary_store_contract (profile : CIL.FeatureProfile) (program : CIL.Program) (index constructor : Nat) (instruction : CIL.Op)
    (operationStep : UnaryStep program instruction)
    (found : program[index]? = some (unaryBody profile instruction constructor))
    (original : Memory) (input output : Reference) (frame : Frame)
    (call : CallingConditions program original [input] [output])
    (disjoint : output.allocation ≠ input.allocation) :
    StoreContract program index original [input] output (unaryArguments input output) frame
      (fun i => ~~~inputLimb original input i) (fun i => 5 + 7 * i) := by
  intro limb positive memory current outside
  have cases : limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  let pc := 5 + 7 * limb.val
  let word := ~~~inputLimb memory input limb
  obtain ⟨stored, written, valid, changed, loaded, retained⟩ := store_limb current limb word []
  have preserved := input_limb_preserved call (by simp : input ∈ [input]) disjoint outside limb
  refine ⟨stored, valid, fun id bound offset beyond => (changed id offset beyond).trans (outside id bound offset beyond),
    by simpa only [word, preserved] using loaded, retained, ?_⟩
  intro final values continuation
  obtain ⟨fuel, finished⟩ := continuation
  have storedRun : run program (fuel + 1) index (pc + 6) (unaryArguments input output) frame
      [.scalar (.i64 word), .reference (.address {output with offset := output.offset + 8 * limb.val})] memory = .ok (final, values) := by
    apply Eq.trans
    · apply run_next (target := pc + 7) (values := []) (nextFrame := frame) (updated := stored) found
        (by rcases cases with rfl | rfl | rfl <;> rfl)
      simp [step, pureArity, written, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simpa [pc, Nat.mul_add, Nat.add_assoc] using finished
  obtain ⟨readFuel, readRun⟩ := unary_limb program instruction operationStep index (pc + 3) (unaryBody profile instruction constructor) found limb
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    memory input output frame [.reference (.address {output with offset := output.offset + 8 * limb.val})] current final values
    ⟨fuel + 1, by simpa [Nat.add_assoc, word] using storedRun⟩
  refine ⟨readFuel + 3, ?_⟩
  change run program (readFuel + 3) index pc (unaryArguments input output) frame [] memory = .ok (final, values)
  have formed := current.output_formed (by simp : output ∈ [output])
  have address := current.output_limb_address (by simp : output ∈ [output]) limb
  have fieldFormed := current.output_limb_formed (by simp : output ∈ [output]) limb
  apply Eq.trans
  · apply run_next (op := .arg 1) (target := pc + 1) (values := [.reference (.address output)]) (nextFrame := frame) (updated := memory) found
      (by rcases cases with rfl | rfl | rfl <;> rfl)
    simp [step, unaryArguments, checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Eq.trans
  · apply run_next (op := .fieldAddress (8 * limb.val)) (target := pc + 2) (values := [.reference (.address {output with offset := output.offset + 8 * limb.val})]) (nextFrame := frame) (updated := memory) found
      (by rcases cases with rfl | rfl | rfl <;> rfl)
    simp [step, pureArity, CIL.Safety.instruction, address, Nat.add_assoc, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Eq.trans
  · apply run_next (op := .memory .asRef) (target := pc + 3) (values := [.reference (.address {output with offset := output.offset + 8 * limb.val})]) (nextFrame := frame) (updated := memory) found
      (by rcases cases with rfl | rfl | rfl <;> rfl)
    simp [step, staticInstruction, memoryInstruction, formValue, fieldFormed, Nat.add_assoc, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact readRun

#print axioms unary_limb
#print axioms unary_store_contract
end UInt256Proof.Bitwise.Early


namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety
theorem unary_result (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index constructor : Nat) (instruction : CIL.Op)
    (operationStep : UnaryStep program instruction)
    (found : program[index]? = some (unaryBody profile instruction constructor))
    (constructorFound : program[constructor]? = some (ConstructorSafety.body profile))
    (memory : Memory) (input output : Reference)
    (call : CallingConditions program memory [input] [output])
    (disjoint : output.allocation ≠ input.allocation) :
    ∃ fuel final, InvocationCertificate program index (unaryArguments input output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (~~~inputValue memory input).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let w := fun i => ~~~inputLimb memory input i
  obtain ⟨temporary, initial, fresh, initialCall, readback, outside, constructed⟩ :=
    ScalarSafety.construct_prefix program index 10 constructor (unaryBody profile instruction constructor) profile
      found constructorFound (by rfl) (by rfl) memory [input] output (unaryArguments input output) (w 0) 0 0 0 call
  let frame : Frame := ⟨memory.nextIdentity, [], [temporary.allocation], []⟩
  have r0 := first_limb initial output (w 0) initialCall.1.1 readback
  obtain ⟨m3, c3, out3, encoded, runStores⟩ := finish_stores program index memory initial [input] output
    (unaryArguments input output) frame w (fun i => 5 + 7 * i) initialCall outside r0
    (unary_store_contract profile program index constructor instruction operationStep found memory input output frame call disjoint)
  have returned : run program 1 index 33 (unaryArguments input output) frame [] m3 = .ok (leaveFrame frame m3, []) := by
    apply run_return found (by rfl) (by rfl) (by rfl)
  have tail := runStores _ [] ⟨1, returned⟩
  obtain ⟨fuel, finished⟩ := constructed _ [] tail
  have prefixRun : ∃ n, run program n index 0 (unaryArguments input output)
      ⟨memory.nextIdentity, [], [], []⟩ [] memory = .ok (leaveFrame frame m3, []) := by
    have zeros : run program (fuel + 6) index 4 (unaryArguments input output) ⟨memory.nextIdentity, [], [], []⟩
        [.scalar (.i64 (w 0)), .reference (.address output)] memory = .ok (leaveFrame frame m3, []) := by
      iterate 6
        apply Eq.trans
        · apply run_next found (by rfl) (by rfl)
      exact finished
    obtain ⟨n, run⟩ := unary_limb program instruction operationStep index 1 (unaryBody profile instruction constructor) found 0 rfl rfl rfl memory input output ⟨memory.nextIdentity, [], [], []⟩ [.reference (.address output)] call _ [] ⟨fuel + 6, zeros⟩
    refine ⟨n + 1, ?_⟩
    apply Eq.trans
    · apply run_next (target := 1) (values := [.reference (.address output)]) (nextFrame := ⟨memory.nextIdentity, [], [], []⟩) (updated := memory) found (by rfl)
      bitwise_step_simp unaryArguments, (call.output_formed (by simp : output ∈ [output]))
    exact run
  obtain ⟨n, executed⟩ := prefixRun
  have checked : (unaryArguments input output).mapM (checkedValue memory) = .ok (unaryArguments input output) := by
    simp [unaryArguments, checkedValue, formValue, call.input_formed (by simp : input ∈ [input]),
       call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (unaryBody profile instruction constructor) (unaryArguments input output) memory =
      .ok (⟨memory.nextIdentity, [], [], []⟩, memory) := rfl
  have after := leaveFrame_preserves_memory_below frame m3 memory.nextIdentity (by
    intro id member; simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at member
    rw [member, fresh]; exact Nat.le_refl _)
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (call.1.2.2 (wordView output) (by simp))
  have old := (call.1.1.1 _ _ present).1
  refine ⟨n, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup (checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup) executed, ?_,
    (after.access output old 32 1 true).trans (c3.1.2.2 (wordView output) (by simp)), ?_⟩
  · have packedNot : packed (w 0) (w 1) (w 2) (w 3) = ~~~inputValue memory input := by
      change UInt256Model.value (fun i => ~~~inputLimb memory input i) = _
      rw [UInt256Proof.Bitwise.value_not]
      exact congrArg (fun value : BitVec 256 => ~~~value) (show UInt256Model.value (inputLimb memory input) = inputValue memory input from UInt256Proof.input_value _ _)
    rw [← packedNot]
    exact (after.read output old 32 1).trans encoded
  · intro id bound offset beyond
    exact (after.cells id bound offset).trans (out3 id bound offset beyond)

#print axioms encoded_limbs
#print axioms unary_result
end UInt256Proof.Bitwise.Early









