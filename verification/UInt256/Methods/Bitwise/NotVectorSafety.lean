import CIL.Safety.Equations
import CIL.Safety.SymbolicExecution
import UInt256.Methods.Bitwise.VectorValues
import UInt256.Safety.UnaryContract

namespace UInt256Proof.Bitwise.NotVectorSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Bitwise.VectorValues

def body (profile : CIL.FeatureProfile)  : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code := [
    .arg 1, .arg 0, .loadAggregate 32, .memory (.bitcastValue (.aggregate 32) .vector256),
    .intrinsic (.vector (.bnot 256)) 1, .memory (.bitcastValue .vector256 (.aggregate 32)),
    .storeAggregate 32, .ret] }

theorem intrinsic_step  (method : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (input : BitVec 256) :
    step method (.intrinsic (.vector (.bnot 256)) 1) pc args frame
      (.scalar (.v256 input) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.v256 ((~~~·) input)) :: rest) frame memory) := by
  rfl

theorem run_leaf (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index : Nat) (found : program[index]? = some (body profile))
    (memory : Memory) (input output : Reference) (frame : Frame)
    (call : CallingConditions program memory [input] [output]) :
    ∃ final,
      run program 8 index 0 (unaryArguments input output) frame [] memory = .ok (leaveFrame frame final, []) ∧
      read final output 32 1 = .ok (numberBytes ((~~~·) (inputValue memory input)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let bits := (~~~·) (inputValue memory input)
  have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨final, written, retained, outside, readback⟩ := call.write_output_slice
    (by simp : output ∈ [output]) 0 (numberBytes bits.toNat 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  refine ⟨final, ?_, readback, retained.1.2.2 (wordView output) (by simp), outside⟩
  simp only [bits, BitVec.toNat_not] at written length
  have fl := call.input_formed (reference := input) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have hl := input_encoded program memory [input] [output] call input (by simp)
  iterate 4
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
            [step, cil_guard, observerCount, unaryArguments, checkedValue, formValue, fl, fo, hl,
             pureArity, instruction, staticInstruction, memoryInstruction, dereference,
             aggregate_to_vector, checkedAt,
             Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl,rfl,rfl,rfl⟩
        done
  apply Eq.trans
  · apply run_next found (by rfl)
    exact intrinsic_step _ _ _ _ _ _ (inputValue memory input)
  iterate 2
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
            [step, cil_guard, observerCount,
             pureArity, instruction, staticInstruction, memoryInstruction, referenceAt,
             vector_to_aggregate, length, written, checkedAt,
             Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl,rfl,rfl,rfl⟩
        done
  apply run_return found (by rfl)
  · rfl
  · rfl

theorem leaf_result (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index : Nat) (found : program[index]? = some (body profile))
    (memory : Memory) (input output : Reference)
    (call : CallingConditions program memory [input] [output]) :
    ∃ final,
      InvocationCertificate program index (unaryArguments input output) memory 8 final [] ∧
      read final output 32 1 = .ok (numberBytes ((~~~·) (inputValue memory input)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  obtain ⟨final, run, loaded, writable, outside⟩ := run_leaf profile program index found memory input output frame call
  have setup : enterFrame (body profile) (unaryArguments input output) memory = .ok (frame, memory) := rfl
  have checked : (unaryArguments input output).mapM (checkedValue memory) = .ok (unaryArguments input output) := by
    simp [unaryArguments, checkedValue, formValue, call.input_formed (by simp : input ∈ [input]),
      call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [leaveFrame, frame, List.foldl_nil] at run
  exact ⟨final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup) run, loaded, writable, outside⟩

def entryBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code :=
    [.feature .vector256Accelerated, .brzero 6, .arg 0, .arg 1, .call callee 2, .ret] ++
      List.replicate 16 (.unsupported "Unreachable under selected profile") }

theorem entry_prefix (profile : CIL.FeatureProfile) (enabled : profile.vector256Accelerated = true)
    (program : CIL.Program) (index callee fuel : Nat) (found : program[index]? = some (entryBody profile callee))
    (memory : Memory) (input output : Reference) (frame : Frame)
    (call : CallingConditions program memory [input] [output]) :
    run program (fuel + 4) index 0 (unaryArguments input output) frame [] memory =
      run program fuel index 4 (unaryArguments input output) frame
        (unaryArguments input output).reverse memory := by
  have fl := call.input_formed (reference := input) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have evaluated : profile.evaluate .vector256Accelerated = true := enabled
  cil_checked_steps 4 [entryBody, unaryArguments, fl, fo, evaluated]
  rfl

theorem entry_result (profile : CIL.FeatureProfile) (enabled : profile.vector256Accelerated = true)
     (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (entryBody profile callee))
    (childFound : program[callee]? = some (body profile))
    (memory : Memory) (input output : Reference)
    (call : CallingConditions program memory [input] [output]) :
    ∃ fuel final,
      InvocationCertificate program index (unaryArguments input output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes ((~~~·) (inputValue memory input)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  obtain ⟨final, child, loaded, writable, outside⟩ := leaf_result profile program callee childFound memory input output call
  have checked : (unaryArguments input output).mapM (checkedValue memory) = .ok (unaryArguments input output) := by
    simp [unaryArguments, checkedValue, formValue, call.input_formed (by simp : input ∈ [input]),
      call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (entryBody profile callee) (.call callee 2) 4 (unaryArguments input output) frame
      (unaryArguments input output).reverse memory = .ok (.call callee (unaryArguments input output) [] memory) := by
    simp only [step, cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, unaryArguments, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.take, List.drop, Bind.bind, Except.bind]
    exact congrArg (fun xs => xs.map fun checked => FrameAction.call callee checked [] memory) checked
  have tail : run program 1 index 5 (unaryArguments input output) frame [] final = .ok (final, []) := by
    have returned := run_return (fuel := 0) (pc := 5) (op := .ret) (stack := []) (updated := final) found (by rfl) (args := unaryArguments input output)
      (frame := frame) (memory := final) (values := []) (by rfl) (by rfl)
    exact returned
  obtain ⟨fuel, finish⟩ := run_call_exists found (by rfl) stepped ⟨8, child.1⟩ ⟨1, tail⟩
  have run := (entry_prefix profile enabled program index callee fuel found memory input output frame call).trans finish
  have setup : enterFrame (entryBody profile callee) (unaryArguments input output) memory = .ok (frame, memory) := rfl
  exact ⟨fuel + 4, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup) run, loaded, writable, outside⟩

theorem correctness (profile : CIL.FeatureProfile) (enabled : profile.vector256Accelerated = true)
     (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (entryBody profile callee))
    (childFound : program[callee]? = some (body profile)) :
    WrappingUnaryContract ((~~~·)) program index := by
  intro memory input output call
  obtain ⟨fuel, final, certificate, loaded, writable, outside⟩ := entry_result profile enabled
    program index callee found childFound memory input output call
  refine ⟨fuel, final, certificate, ?_, writable, fun id _ offset away => outside id offset away⟩
  have decoded := output_snapshot_value final output _ loaded
  rw [byteNumber_numberBytes] at decoded
  simpa only [show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using decoded.symm

#print axioms run_leaf
#print axioms leaf_result
#print axioms entry_result
#print axioms correctness
end UInt256Proof.Bitwise.NotVectorSafety
