import UInt256.Methods.Compare.PrimitiveSafetyContract
import CIL.Safety.CallComposition
import CIL.Safety.NegationReturn

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

def wrapperCall : Nat := Extracted.entryBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

def wrapperNegate : Bool := Extracted.entryBody.code.any fun op =>
  match op with | .eq => true | _ => false

def wrapperReversed : Bool := match (Extracted.entryBody.code[0]? : Option CIL.Op) with
  | some (.arg 1) => true | _ => false

def wrapperScalarFirst : Bool := leafScalarFirst != wrapperReversed

def Prefix {α : Type} (encode : α → CIL.Value) (widen : α → BitVec 64) : Prop :=
  ∀ memory input word frame, CallingConditions Extracted.program memory [input] [] →
    ∀ post : Memory → List Value → Prop,
      (∃ fuel final values, run Extracted.program fuel Extracted.entryIndex wrapperCall
        (scalarOperatorArguments wrapperScalarFirst input (encode word)) frame
        (scalarOperatorArguments leafScalarFirst input (.i64 (widen word))).reverse memory =
          .ok (final, values) ∧ post final values) →
      ∃ fuel final values, run Extracted.program fuel Extracted.entryIndex 0
        (scalarOperatorArguments wrapperScalarFirst input (encode word)) frame [] memory =
          .ok (final, values) ∧ post final values

theorem wrapper_return (args : List Value) (less : Bool) (frame : Frame) (memory : Memory) :
    run Extracted.program 3 Extracted.entryIndex (wrapperCall + 1) args frame
      [.scalar (.i32 (if less then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if less != wrapperNegate then 1 else 0))]) := by
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have returns : Extracted.entryBody.returnsValue = true := by rfl
  first
    | (have polarity : wrapperNegate = false := by rfl
       have returned : Extracted.entryBody.code[wrapperCall + 1]? = some .ret := by rfl
       rw [polarity]
       cases less <;> simp [run, found, returned, returns, step, checkedValue, numericValue,
         Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
    | (have polarity : wrapperNegate = true := by rfl
       have result := run_negation_return Extracted.program Extracted.entryIndex (wrapperCall + 1)
         Extracted.entryBody found (by rfl) (by rfl) (by rfl) returns args frame memory
         (if less then 1 else 0)
       rw [polarity]
       cases less <;> simpa using result)

theorem wrapper_checked {α : Type} (encode : α → CIL.Value) (widen : α → BitVec 64)
    (numeric : ∀ word, numericValue (encode word) = true) (prefixTrace : Prefix encode widen) :
    ScalarOperatorContract wrapperScalarFirst wrapperNegate encode
      (fun input word => predicate leafSigned leafScalarFirst input (widen word))
      Extracted.program Extracted.entryIndex := by
  intro memory input word call
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have kinds : Extracted.entryBody.localKinds = [] := by rfl
  have locals : Extracted.entryBody.locals = [] := by rfl
  have arguments : Extracted.entryBody.aggregateArgs = [] := by rfl
  have setup : enterFrame Extracted.entryBody
      (scalarOperatorArguments wrapperScalarFirst input (encode word)) memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, locals, arguments, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have formed := call.input_formed (reference := input) (by simp)
  have checked : (scalarOperatorArguments wrapperScalarFirst input (encode word)).mapM (checkedValue memory) =
      .ok (scalarOperatorArguments wrapperScalarFirst input (encode word)) := by
    cases order : wrapperScalarFirst <;>
      simp [scalarOperatorArguments, scalarArguments, checkedValue, numeric, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨childFuel, final, certificate, cells⟩ := leaf_checked memory input (widen word) call
  have positive (flag : Bool) : (flag != false) = flag := by cases flag <;> rfl
  simp only [positive] at certificate
  have fetched : Extracted.entryBody.code[wrapperCall]? = some (.call leafIndex 2) := by rfl
  have stepped : step Extracted.entryBody (.call leafIndex 2) wrapperCall
      (scalarOperatorArguments wrapperScalarFirst input (encode word)) frame
      (scalarOperatorArguments leafScalarFirst input (.i64 (widen word))).reverse memory =
      .ok (.call leafIndex (scalarOperatorArguments leafScalarFirst input (.i64 (widen word))) [] memory) := by
    cases order : leafScalarFirst <;>
      simp [step, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩
    ⟨3, wrapper_return _ _ frame final⟩
  let post : Memory → List Value → Prop := fun result values => result = leaveFrame frame final ∧
    values = [.scalar (.i32 (if predicate leafSigned leafScalarFirst (inputValue memory input) (widen word)
      != wrapperNegate then 1 else 0))]
  obtain ⟨fuel, result, values, finished, sameMemory, sameValues⟩ :=
    prefixTrace memory input word frame call post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst result
  subst values
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  simpa only [leaveFrame, frame, List.foldl_nil] using cells

#print axioms wrapper_return
#print axioms wrapper_checked
end UInt256Proof.Compare.PrimitiveSafety
