import UInt256.Methods.Compare.PrimitiveArithmetic
import UInt256.Methods.Compare.PrimitiveLeaf
import UInt256.Safety.CallerSetup


namespace UInt256Proof.Compare.PrimitiveLeaf
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

theorem result_math (leafSigned leafScalarFirst : Bool) (memory : Memory) (input : Reference) (word : BitVec 64) :
    result leafSigned leafScalarFirst memory input word =
      if predicate leafSigned leafScalarFirst (inputValue memory input) word then 1 else 0 := by
  have same : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  have result := limbs_result_math leafSigned leafScalarFirst (inputLimb memory input) word
  rw [same] at result
  exact result

theorem checked_template (leafSigned leafScalarFirst : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (method leafSigned leafScalarFirst)) : ScalarOperatorContract leafScalarFirst false CIL.Value.i64
    (predicate leafSigned leafScalarFirst) program index := by
  intro memory input word call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  let leafBody := method leafSigned leafScalarFirst
  have kinds : leafBody.localKinds = [] := by cases leafSigned <;> cases leafScalarFirst <;> rfl
  have values : leafBody.locals = [] := by cases leafSigned <;> cases leafScalarFirst <;> rfl
  have vectors : leafBody.vectorArgs = [] := by cases leafSigned <;> cases leafScalarFirst <;> rfl
  have arguments : leafBody.parameterHomes = [] := by cases leafSigned <;> cases leafScalarFirst <;> rfl
  have opaqueLocals : leafBody.opaqueVectorLocals = [] := by cases leafSigned <;> cases leafScalarFirst <;> rfl
  have setup : enterFrame leafBody (scalarOperatorArguments leafScalarFirst input (.i64 word)) memory =
      .ok (frame, memory) := by
    simp [enterFrame, kinds, values, vectors, arguments, opaqueLocals, makeSelectedLocals, makeLocals, makeArgumentHomes, makeParameterHomes, frame, cil_code,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have formed := call.input_formed (reference := input) (by simp)
  have checked : (scalarOperatorArguments leafScalarFirst input (.i64 word)).mapM (checkedValue memory) =
      .ok (scalarOperatorArguments leafScalarFirst input (.i64 word)) := by
    cases order : leafScalarFirst <;>
      simp [scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have finished := run_template leafSigned leafScalarFirst program index found memory input word frame call
  rw [result_math] at finished
  simp only [leaveFrame, frame, List.foldl_nil] at finished
  refine ⟨22, memory, ?_, fun _ _ _ => rfl⟩
  have certificate := certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished
  simpa using certificate

#print axioms result_math
#print axioms checked_template
end UInt256Proof.Compare.PrimitiveLeaf
