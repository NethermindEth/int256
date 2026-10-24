import CIL.Safety.Equations
import CIL.Safety.SymbolicExecution
import UInt256.Methods.Bitwise.VectorValues

namespace UInt256Proof.Bitwise.VectorSafety
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise UInt256Proof.Bitwise.VectorValues

def intrinsic : Binary → CIL.Intrinsic
  | .and => .vector (.band 256)
  | .or => .vector (.bor 256)
  | .xor => .vector (.bxor 256)

def body (profile : CIL.FeatureProfile) (operation : Binary) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code := [
    .arg 2, .arg 0, .loadAggregate 32, .memory (.bitcastValue (.aggregate 32) .vector256),
    .arg 1, .loadAggregate 32, .memory (.bitcastValue (.aggregate 32) .vector256),
    .intrinsic (intrinsic operation) 2, .memory (.bitcastValue .vector256 (.aggregate 32)),
    .storeAggregate 32, .ret] }

theorem intrinsic_step (operation : Binary) (method : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (left right : BitVec 256) :
    step method (.intrinsic (intrinsic operation) 2) pc args frame
      (.scalar (.v256 right) :: .scalar (.v256 left) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.v256 (applyBinary operation left right)) :: rest) frame memory) := by
  cases operation <;> rfl

theorem run_leaf (profile : CIL.FeatureProfile) (operation : Binary)
    (program : CIL.Program) (index : Nat) (found : program[index]? = some (body profile operation))
    (memory : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left,right] [output]) :
    ∃ final,
      run program 11 index 0 (binaryArguments left right output) frame [] memory = .ok (leaveFrame frame final, []) ∧
      read final output 32 1 = .ok (numberBytes (applyBinary operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let bits := applyBinary operation (inputValue memory left) (inputValue memory right)
  have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨final, written, retained, outside, readback⟩ := call.write_output_slice
    (by simp : output ∈ [output]) 0 (numberBytes bits.toNat 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  refine ⟨final, ?_, readback, retained.1.2.2 (wordView output) (by simp), outside⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have hl := input_encoded program memory [left,right] [output] call left (by simp)
  have hr := input_encoded program memory [left,right] [output] call right (by simp)
  iterate 10
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · first
        | exact intrinsic_step operation _ _ _ _ _ _ _ _
        | (simp (config := { implicitDefEqProofs := false })
            [step, cil_guard, observerCount, binaryArguments, checkedValue, formValue, fl, fr, fo, hl, hr,
             pureArity, instruction, staticInstruction, memoryInstruction, dereference, referenceAt,
             aggregate_to_vector, vector_to_aggregate, length, written, bits, checkedAt,
             Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try exact ⟨rfl,rfl,rfl,rfl⟩
           done)
  apply run_return found (by rfl)
  · rfl
  · rfl

theorem leaf_result (profile : CIL.FeatureProfile) (operation : Binary)
    (program : CIL.Program) (index : Nat) (found : program[index]? = some (body profile operation))
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left,right] [output]) :
    ∃ final,
      InvocationCertificate program index (binaryArguments left right output) memory 11 final [] ∧
      read final output 32 1 = .ok (numberBytes (applyBinary operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  obtain ⟨final, run, loaded, writable, outside⟩ := run_leaf profile operation program index found memory left right output frame call
  have setup : enterFrame (body profile operation) (binaryArguments left right output) memory = .ok (frame, memory) := rfl
  have checked : (binaryArguments left right output).mapM (checkedValue memory) = .ok (binaryArguments left right output) := by
    simp [binaryArguments, checkedValue, formValue, call.input_formed (by simp : left ∈ [left,right]),
      call.input_formed (by simp : right ∈ [left,right]), call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [leaveFrame, frame, List.foldl_nil] at run
  exact ⟨final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (call.binary_entry_live setup) run, loaded, writable, outside⟩

def entryBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code :=
    [.feature .vector256Accelerated, .brzero 7, .arg 0, .arg 1, .arg 2, .call callee 3, .ret] ++
      List.replicate 24 (.unsupported "Unreachable under selected profile") }

theorem entry_prefix (profile : CIL.FeatureProfile) (enabled : profile.vector256Accelerated = true)
    (program : CIL.Program) (index callee fuel : Nat) (found : program[index]? = some (entryBody profile callee))
    (memory : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left,right] [output]) :
    run program (fuel + 5) index 0 (binaryArguments left right output) frame [] memory =
      run program fuel index 5 (binaryArguments left right output) frame
        (binaryArguments left right output).reverse memory := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have evaluated : profile.evaluate .vector256Accelerated = true := enabled
  cil_checked_steps 5 [entryBody, binaryArguments, fl, fr, fo, evaluated]
  rfl

theorem entry_result (profile : CIL.FeatureProfile) (enabled : profile.vector256Accelerated = true)
    (operation : Binary) (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (entryBody profile callee))
    (childFound : program[callee]? = some (body profile operation))
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left,right] [output]) :
    ∃ fuel final,
      InvocationCertificate program index (binaryArguments left right output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (applyBinary operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, OutsideOutput output id offset → final.cells id offset = memory.cells id offset := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  obtain ⟨final, child, loaded, writable, outside⟩ := leaf_result profile operation program callee childFound memory left right output call
  have checked : (binaryArguments left right output).mapM (checkedValue memory) = .ok (binaryArguments left right output) := by
    simp [binaryArguments, checkedValue, formValue, call.input_formed (by simp : left ∈ [left,right]),
      call.input_formed (by simp : right ∈ [left,right]), call.output_formed (by simp : output ∈ [output]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (entryBody profile callee) (.call callee 3) 5 (binaryArguments left right output) frame
      (binaryArguments left right output).reverse memory = .ok (.call callee (binaryArguments left right output) [] memory) := by
    simp only [step, cil_guard, observerCount, Bool.or_false, Bool.false_eq_true, binaryArguments, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.lt_irrefl, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.take, List.drop, Bind.bind, Except.bind]
    exact congrArg (fun xs => xs.map fun checked => FrameAction.call callee checked [] memory) checked
  have tail : run program 1 index 6 (binaryArguments left right output) frame [] final = .ok (final, []) := by
    have returned := run_return (fuel := 0) (pc := 6) (op := .ret) (stack := []) (updated := final) found (by rfl) (args := binaryArguments left right output)
      (frame := frame) (memory := final) (values := []) (by rfl) (by rfl)
    exact returned
  obtain ⟨fuel, finish⟩ := run_call_exists found (by rfl) stepped ⟨11, child.1⟩ ⟨1, tail⟩
  have run := (entry_prefix profile enabled program index callee fuel found memory left right output frame call).trans finish
  have setup : enterFrame (entryBody profile callee) (binaryArguments left right output) memory = .ok (frame, memory) := rfl
  exact ⟨fuel + 5, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (call.binary_entry_live setup) run, loaded, writable, outside⟩

theorem correctness (profile : CIL.FeatureProfile) (enabled : profile.vector256Accelerated = true)
    (operation : Binary) (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (entryBody profile callee))
    (childFound : program[callee]? = some (body profile operation)) :
    WrappingBinaryContract (applyBinary operation) program index := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, loaded, writable, outside⟩ := entry_result profile enabled operation
    program index callee found childFound memory left right output call
  refine ⟨fuel, final, certificate, ?_, writable, fun id _ offset away => outside id offset away⟩
  have decoded := output_snapshot_value final output _ loaded
  rw [byteNumber_numberBytes] at decoded
  simpa only [show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
    BitVec.ofNat_toNat, BitVec.setWidth_eq] using decoded.symm

#print axioms run_leaf
#print axioms leaf_result
#print axioms entry_result
#print axioms correctness
end UInt256Proof.Bitwise.VectorSafety
