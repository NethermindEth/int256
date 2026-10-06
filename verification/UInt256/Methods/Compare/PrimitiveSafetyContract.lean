import UInt256.Methods.Compare.PrimitiveSafetyLeaf
import UInt256.Methods.Compare.PrimitiveSafetyMath
import UInt256.Safety.CallerSetup

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

theorem leaf_result_math (memory : Memory) (input : Reference) (word : BitVec 64) :
    leafResult memory input word =
      if predicate leafSigned leafScalarFirst (inputValue memory input) word then 1 else 0 := by
  have same : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  have result := limbs_result_math leafSigned leafScalarFirst (inputLimb memory input) word
  rw [same] at result
  exact result

theorem leaf_checked : ScalarOperatorContract leafScalarFirst false CIL.Value.i64
    (predicate leafSigned leafScalarFirst) Extracted.program leafIndex := by
  intro memory input word call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[leafIndex]? = some leafBody := by rfl
  have kinds : leafBody.localKinds = [] := by rfl
  have values : leafBody.locals = [] := by rfl
  have arguments : leafBody.aggregateArgs = [] := by rfl
  have setup : enterFrame leafBody (scalarOperatorArguments leafScalarFirst input (.i64 word)) memory =
      .ok (frame, memory) := by
    simp [enterFrame, kinds, values, arguments, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have formed := call.input_formed (reference := input) (by simp)
  have checked : (scalarOperatorArguments leafScalarFirst input (.i64 word)).mapM (checkedValue memory) =
      .ok (scalarOperatorArguments leafScalarFirst input (.i64 word)) := by
    cases order : leafScalarFirst <;>
      simp [scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have finished := leaf_run memory input word frame call
  rw [leaf_result_math] at finished
  simp only [leaveFrame, frame, List.foldl_nil] at finished
  refine ⟨22, memory, ?_, fun _ _ _ => rfl⟩
  have certificate := certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished
  simpa using certificate

#print axioms leaf_result_math
#print axioms leaf_checked
end UInt256Proof.Compare.PrimitiveSafety
