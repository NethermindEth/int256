import UInt256.Methods.Bitwise.EarlyStoreMemory
import CIL.Safety.CallComposition
namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise

def plainWordBody (profile : CIL.FeatureProfile) (operation : Binary) : CIL.Method :=
  {profile, returnsValue := true, locals := [], code := [.arg 0, .arg 1, opcode operation, .ret]}

theorem plain_word (profile : CIL.FeatureProfile) (operation : Binary)
    (program : CIL.Program) (index : Nat) (found : program[index]? = some (plainWordBody profile operation))
    (memory : Memory) (a b : BitVec 64) :
    invoke program 4 index [.scalar (.i64 a), .scalar (.i64 b)] memory =
      .ok (memory, [.scalar (.i64 (wordOperation operation a b))]) := by
  simp only [invoke, found]
  change run program 4 index 0 [.scalar (.i64 a), .scalar (.i64 b)] ⟨memory.nextIdentity, [], [], []⟩ [] memory = _
  iterate 2
    apply Eq.trans
    · apply run_next found (by rfl) (by rfl)
  apply Eq.trans
  · apply run_next found (by rfl) (word_step operation _ _ _ _ _ _ a b)
  rw [run]
  simp only [found]
  rfl

def BinaryStep (operation : Binary) (program : CIL.Program) (instruction : CIL.Op) : Prop :=
  ∀ index pc body, program[index]? = some body → body.code[pc]? = some instruction →
    ∀ memory frame args rest a b final values,
      (∃ fuel, run program fuel index (pc + 1) args frame
        (.scalar (.i64 (wordOperation operation a b)) :: rest) memory = .ok (final, values)) →
      ∃ fuel, run program fuel index pc args frame
        (.scalar (.i64 b) :: .scalar (.i64 a) :: rest) memory = .ok (final, values)

theorem inline_binary (operation : Binary) (program : CIL.Program) :
    BinaryStep operation program (opcode operation) := by
  intro index pc body found fetched memory frame args rest a b final values continuation
  obtain ⟨fuel, finished⟩ := continuation
  exact ⟨fuel + 1, (run_next found fetched (word_step operation _ _ _ _ _ _ a b)).trans finished⟩

theorem helper_binary (operation : Binary) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (helper : Nat) (foundHelper : program[helper]? = some (plainWordBody profile operation)) :
    BinaryStep operation program (.call helper 2) := by
  intro index pc body found fetched memory frame args rest a b final values continuation
  apply run_call_exists found fetched (by rfl)
    ⟨4, plain_word profile operation program helper foundHelper memory a b⟩
  simpa using continuation

theorem binary_limb (operation : Binary) (program : CIL.Program) (instruction : CIL.Op)
    (operationStep : BinaryStep operation program instruction)
    (index pc : Nat) (body : CIL.Method) (found : program[index]? = some body)
    (limb : Fin 4)
    (h0 : body.code[pc]? = some (.arg 0))
    (h1 : body.code[pc + 1]? = some (.fieldAt (8 * limb.val) 8))
    (h2 : body.code[pc + 2]? = some (.arg 1))
    (h3 : body.code[pc + 3]? = some (.fieldAt (8 * limb.val) 8))
    (h4 : body.code[pc + 4]? = some instruction)
    (memory : Memory) (left right output : Reference) (frame : Frame) (rest : List Value)
    (call : CallingConditions program memory [left, right] [output]) (final : Memory) (values : List Value)
    (continuation : ∃ fuel, run program fuel index (pc + 5) (binaryArguments left right output) frame
      (.scalar (.i64 (wordOperation operation (inputLimb memory left limb) (inputLimb memory right limb))) :: rest)
      memory = .ok (final, values)) :
    ∃ fuel, run program fuel index pc (binaryArguments left right output) frame rest memory = .ok (final, values) := by
  have tail := operationStep index (pc + 4) body found h4 memory frame (binaryArguments left right output) rest
    (inputLimb memory left limb) (inputLimb memory right limb) final values (by simpa [Nat.add_assoc] using continuation)
  obtain ⟨fuel, finished⟩ := tail
  exact ⟨fuel + 4, (read_pair program index pc fuel body found limb h0 h1 h2 h3 memory left right output frame rest call).trans finished⟩

end UInt256Proof.Bitwise.Early
namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise

theorem store_binary_limb (operation : Binary) (program : CIL.Program) (instruction : CIL.Op)
    (operationStep : BinaryStep operation program instruction)
    (index pc : Nat) (body : CIL.Method) (found : program[index]? = some body)
    (limb : Fin 4)
    (h0 : body.code[pc]? = some (.arg 2))
    (h1 : body.code[pc + 1]? = some (.fieldAddress (8 * limb.val)))
    (h2 : body.code[pc + 2]? = some (.memory .asRef))
    (h3 : body.code[pc + 3]? = some (.arg 0))
    (h4 : body.code[pc + 4]? = some (.fieldAt (8 * limb.val) 8))
    (h5 : body.code[pc + 5]? = some (.arg 1))
    (h6 : body.code[pc + 6]? = some (.fieldAt (8 * limb.val) 8))
    (h7 : body.code[pc + 7]? = some instruction)
    (h8 : body.code[pc + 8]? = some .store64)
    (memory : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ stored,
      CallingConditions program stored [left, right] [output] ∧
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = memory.cells id offset) ∧
      read stored { output with offset := output.offset + 8 * limb.val } 8 1 =
        .ok (numberBytes (wordOperation operation (inputLimb memory left limb) (inputLimb memory right limb)).toNat 8) ∧
      (∀ other : Fin 4, other ≠ limb → ∀ bytes,
        read memory { output with offset := output.offset + 8 * other.val } 8 1 = .ok bytes →
        read stored { output with offset := output.offset + 8 * other.val } 8 1 = .ok bytes) ∧
      ∀ final values, (∃ fuel, run program fuel index (pc + 9) (binaryArguments left right output) frame [] stored = .ok (final, values)) →
        ∃ fuel, run program fuel index pc (binaryArguments left right output) frame [] memory = .ok (final, values) := by
  let word := wordOperation operation (inputLimb memory left limb) (inputLimb memory right limb)
  obtain ⟨stored, written, valid, outside, loaded, retained⟩ := store_limb call limb word []
  refine ⟨stored, valid, outside, loaded, retained, ?_⟩
  intro final values continuation
  obtain ⟨fuel, finished⟩ := continuation
  have storedRun : run program (fuel + 1) index (pc + 8) (binaryArguments left right output) frame
      [.scalar (.i64 word), .reference (.address {output with offset := output.offset + 8 * limb.val})] memory = .ok (final, values) := by
    apply Eq.trans
    · apply run_next (target := pc + 9) (values := []) (nextFrame := frame) (updated := stored) found h8
      simp [step, pureArity, written, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact finished
  obtain ⟨readFuel, readRun⟩ := binary_limb operation program instruction operationStep index (pc + 3) body found limb
    h3 (by simpa [Nat.add_assoc] using h4) (by simpa [Nat.add_assoc] using h5)
    (by simpa [Nat.add_assoc] using h6) (by simpa [Nat.add_assoc] using h7)
    memory left right output frame [.reference (.address {output with offset := output.offset + 8 * limb.val})]
    call final values ⟨fuel + 1, by simpa [Nat.add_assoc, word] using storedRun⟩
  refine ⟨readFuel + 3, ?_⟩
  have formed := call.output_formed (by simp : output ∈ [output])
  have address := call.output_limb_address (by simp : output ∈ [output]) limb
  have fieldFormed := call.output_limb_formed (by simp : output ∈ [output]) limb
  apply Eq.trans
  · apply run_next (target := pc + 1) (values := [.reference (.address output)]) (nextFrame := frame) (updated := memory) found h0
    bitwise_step_simp formed
  apply Eq.trans
  · apply run_next (target := pc + 2) (values := [.reference (.address {output with offset := output.offset + 8 * limb.val})]) (nextFrame := frame) (updated := memory) found h1
    simp [step, pureArity, CIL.Safety.instruction, address, Nat.add_assoc, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply Eq.trans
  · apply run_next (target := pc + 3) (values := [.reference (.address {output with offset := output.offset + 8 * limb.val})]) (nextFrame := frame) (updated := memory) found h2
    simp [step, memoryInstruction, staticInstruction, formValue, fieldFormed, Nat.add_assoc, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact readRun

#print axioms store_binary_limb
end UInt256Proof.Bitwise.Early



namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise UInt256Proof.ConstructorSafety

def binaryBody (profile : CIL.FeatureProfile) (instruction : CIL.Op) (constructor : Nat) : CIL.Method :=
  {profile, returnsValue := false, locals := [], code := [
    .arg 2, .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, instruction,
    .const32 0, .convI8, .const32 0, .convI8, .const32 0, .convI8,
    .newAggregate constructor 4 32, .storeAggregate 32,
    .arg 2, .fieldAddress 8, .memory .asRef, .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, instruction, .store64,
    .arg 2, .fieldAddress 16, .memory .asRef, .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, instruction, .store64,
    .arg 2, .fieldAddress 24, .memory .asRef, .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, instruction, .store64,
    .ret]}

end UInt256Proof.Bitwise.Early
namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise UInt256Proof.ConstructorSafety

theorem binary_store_contract (operation : Binary) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index constructor : Nat) (instruction : CIL.Op)
    (found : program[index]? = some (binaryBody profile instruction constructor))
    (operationStep : BinaryStep operation program instruction)
    (original : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program original [left,right] [output])
    (dl : output.allocation ≠ left.allocation) (dr : output.allocation ≠ right.allocation) :
    StoreContract program index original [left,right] output (binaryArguments left right output) frame
      (fun i => wordOperation operation (inputLimb original left i) (inputLimb original right i)) (fun i => 5 + 9 * i) := by
  intro limb positive memory current outside
  have cases : limb = 1 ∨ limb = 2 ∨ limb = 3 := by omega
  obtain ⟨stored, valid, changed, loaded, retained, executed⟩ := store_binary_limb operation program instruction operationStep index (5 + 9 * limb.val)
    (binaryBody profile instruction constructor) found limb
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    (by rcases cases with rfl | rfl | rfl <;> rfl)
    memory left right output frame current
  rw [input_limb_preserved call (by simp : left ∈ [left,right]) dl outside,
    input_limb_preserved call (by simp : right ∈ [left,right]) dr outside] at loaded
  exact ⟨stored, valid, fun id bound offset beyond => (changed id offset beyond).trans (outside id bound offset beyond),
    loaded, retained, by simpa [Nat.mul_add, Nat.add_assoc] using executed⟩

#print axioms binary_store_contract
theorem binary_result (operation : Binary) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index constructor : Nat) (instruction : CIL.Op)
    (found : program[index]? = some (binaryBody profile instruction constructor))
    (constructorFound : program[constructor]? = some (ConstructorSafety.body profile))
    (operationStep : BinaryStep operation program instruction)
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left,right] [output])
    (dl : output.allocation ≠ left.allocation) (dr : output.allocation ≠ right.allocation) :
    ∃ fuel final, InvocationCertificate program index (binaryArguments left right output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (applyBinary operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let w := fun i => wordOperation operation (inputLimb memory left i) (inputLimb memory right i)
  obtain ⟨temporary, initial, fresh, initialCall, readback, outside, constructed⟩ :=
    ScalarSafety.construct_prefix program index 12 constructor (binaryBody profile instruction constructor) profile
      found constructorFound (by rfl) (by rfl) memory [left,right] output (binaryArguments left right output) (w 0) 0 0 0 call
  let frame : Frame := ⟨memory.nextIdentity, [], [temporary.allocation], []⟩
  have r0 := first_limb initial output (w 0) initialCall.1.1 readback
  obtain ⟨m3, c3, out3, encoded, runStores⟩ := finish_stores program index memory initial [left,right] output
    (binaryArguments left right output) frame w (fun i => 5 + 9 * i) initialCall outside r0
    (binary_store_contract operation profile program index constructor instruction found operationStep memory left right output frame call dl dr)
  have returned : run program 1 index 41 (binaryArguments left right output) frame [] m3 = .ok (leaveFrame frame m3, []) := by
    apply run_return found (by rfl) (by rfl) (by rfl)
  have tail := runStores _ [] ⟨1, returned⟩
  obtain ⟨fuel, finished⟩ := constructed _ [] tail
  have prefixRun : ∃ n, run program n index 0 (binaryArguments left right output)
      ⟨memory.nextIdentity, [], [], []⟩ [] memory = .ok (leaveFrame frame m3, []) := by
    have zeros : run program (fuel + 6) index 6 (binaryArguments left right output) ⟨memory.nextIdentity, [], [], []⟩
        [.scalar (.i64 (w 0)), .reference (.address output)] memory = .ok (leaveFrame frame m3, []) := by
      iterate 6
        apply Eq.trans
        · apply run_next found (by rfl) (by rfl)
      exact finished
    obtain ⟨n, run⟩ := binary_limb operation program instruction operationStep index 1 (binaryBody profile instruction constructor) found
      0 rfl rfl rfl rfl rfl memory left right output ⟨memory.nextIdentity, [], [], []⟩ [.reference (.address output)] call _ [] ⟨fuel + 6, zeros⟩
    refine ⟨n + 1, ?_⟩
    apply Eq.trans
    · apply run_next (target := 1) (values := [.reference (.address output)]) (nextFrame := ⟨memory.nextIdentity, [], [], []⟩) (updated := memory) found (by rfl)
      bitwise_step_simp (call.output_formed (by simp : output ∈ [output]))
    exact run
  obtain ⟨n, executed⟩ := prefixRun
  have checked : (binaryArguments left right output).mapM (checkedValue memory) = .ok (binaryArguments left right output) := by
    simp [binaryArguments, checkedValue, formValue, call.input_formed (by simp : left ∈ [left,right]),
      call.input_formed (by simp : right ∈ [left,right]), call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (binaryBody profile instruction constructor) (binaryArguments left right output) memory =
      .ok (⟨memory.nextIdentity, [], [], []⟩, memory) := rfl
  have after := leaveFrame_preserves_memory_below frame m3 memory.nextIdentity (by
    intro id member; simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at member
    rw [member, fresh]; exact Nat.le_refl _)
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (call.1.2.2 (wordView output) (by simp))
  have old := (call.1.1.1 _ _ present).1
  refine ⟨n, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup (call.binary_entry_live setup) executed, ?_,
    (after.access output old 32 1 true).trans (c3.1.2.2 (wordView output) (by simp)), ?_⟩
  · rw [← packed_operation operation memory left right]
    exact (after.read output old 32 1).trans encoded
  · intro id bound offset beyond
    exact (after.cells id bound offset).trans (out3 id bound offset beyond)

#print axioms encoded_limbs
#print axioms binary_result
end UInt256Proof.Bitwise.Early
