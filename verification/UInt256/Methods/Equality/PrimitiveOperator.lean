import UInt256.Safety.StepEquation
import UInt256.Methods.Equality.UnsignedPrimitive

namespace UInt256Proof.Equality.PrimitiveOperator
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (reversed negate : Bool) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [],
    code := [ .arg (if reversed then 1 else 0), .arg (if reversed then 0 else 1), .call callee 2 ] ++
      (if negate then [.const32 0, .eq, .ret (some .unsigned8)] else [.ret (some .unsigned8)]) }

theorem returned (profile : CIL.FeatureProfile) (reversed negate : Bool) (program : CIL.Program)
    (entry callee : Nat) (found : program[entry]? = some (body profile reversed negate callee))
    (args : List Value) (flag : Bool) (frame : Frame) (memory : Memory) :
    run program 3 entry 3 args frame [.scalar (.i32 (if flag then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if flag != negate then 1 else 0))]) := by
  cases reversed <;> cases negate <;> cases flag <;>
    simp [run, found, body, step, pureArity, scalars, CIL.step.eq_def, CIL.binary,
      CIL.NarrowKind.extend, instruction, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem prefix_trace {α : Type} (encode : α → CIL.Value)
    (profile : CIL.FeatureProfile) (reversed negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body profile reversed negate callee))
    (numeric : ∀ word, numericValue (encode word) = true)
    (memory : Memory) (input : Reference) (word : α) (frame : Frame)
    (call : CallingConditions program memory [input] []) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values, run program fuel entry 2
      (scalarOperatorArguments reversed input (encode word)) frame
      [.scalar (encode word), .reference (.address input)] memory = .ok (final, values) ∧ post final values) :
    ∃ fuel final values, run program fuel entry 0
      (scalarOperatorArguments reversed input (encode word)) frame [] memory = .ok (final, values) ∧ post final values := by
  have formed := call.input_formed (reference := input) (by simp)
  cases reversed
  all_goals
    repeat' first
      | exact continuation
      | (apply run_next_exists post found
         · simp only [body]; rfl
         · simp [body, step, scalarOperatorArguments, scalarArguments, numeric, checkedValue, formValue, formed,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           exact ⟨rfl, rfl, rfl, rfl⟩)

theorem checked {α : Type} (encode : α → CIL.Value) (equal : BitVec 256 → α → Bool)
    (profile : CIL.FeatureProfile) (reversed negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body profile reversed negate callee))
    (numeric : ∀ word, numericValue (encode word) = true)
    (child : ScalarOperatorContract false false encode equal program callee) :
    ScalarOperatorContract reversed negate encode equal program entry := by
  intro memory input word call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have setup : enterFrame (body profile reversed negate callee)
      (scalarOperatorArguments reversed input (encode word)) memory = .ok (frame, memory) := by
    simp [enterFrame, body, makeLocals, makeArgumentHomes, makeParameterHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have formed := call.input_formed (reference := input) (by simp)
  have checked : (scalarOperatorArguments reversed input (encode word)).mapM (checkedValue memory) =
      .ok (scalarOperatorArguments reversed input (encode word)) := by
    cases reversed <;>
      simp [scalarOperatorArguments, scalarArguments, checkedValue, numeric, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨childFuel, final, certificate, cells⟩ := child memory input word call
  simp only [Bool.bne_false] at certificate
  have fetched : (body profile reversed negate callee).code[2]? = some (.call callee 2) := by
    cases reversed <;> rfl
  have stepped : step (body profile reversed negate callee) (.call callee 2) 2
      (scalarOperatorArguments reversed input (encode word)) frame
      [.scalar (encode word), .reference (.address input)] memory =
      .ok (.call callee (scalarOperatorArguments false input (encode word)) [] memory) := by
    simp [step, scalarOperatorArguments, scalarArguments, checkedValue, numeric, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩
    ⟨3, returned profile reversed negate program entry callee found _ _ frame final⟩
  let post : Memory → List Value → Prop := fun result values => result = leaveFrame frame final ∧
    values = [.scalar (.i32 (if equal (inputValue memory input) word != negate then 1 else 0))]
  obtain ⟨fuel, result, values, finished, sameMemory, sameValues⟩ :=
    prefix_trace encode profile reversed negate program entry callee found numeric memory input word frame call post
      ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst result
  subst values
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  simpa only [leaveFrame, frame, List.foldl_nil] using cells

#print axioms returned
#print axioms prefix_trace
#print axioms checked
end UInt256Proof.Equality.PrimitiveOperator
