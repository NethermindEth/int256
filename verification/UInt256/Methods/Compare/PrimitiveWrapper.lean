import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.Compare.PrimitiveLeafContract
import CIL.Safety.CallComposition
import CIL.Safety.GuardNormalization

namespace UInt256Proof.Compare.PrimitiveWrapper
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

def prefixCode (narrow signed scalarFirst reversed : Bool) : List CIL.Op :=
  let first := if reversed then 1 else 0
  let second := if reversed then 0 else 1
  let convert := if signed then CIL.Op.convI8 else CIL.Op.convU8
  if narrow then
    if scalarFirst then [.arg first, convert, .arg second]
    else [.arg first, .arg second, convert]
  else [.arg first, .arg second]

def suffix (negate : Bool) : List CIL.Op :=
  if negate then [.const32 0, .eq, .ret (some .unsigned8)] else [.ret (some .unsigned8)]

def callPC (narrow : Bool) : Nat := if narrow then 3 else 2

def method (narrow signed scalarFirst reversed negate : Bool) (callee : Nat) : CIL.Method :=
  { profile := PrimitiveLeaf.scalarProfile, returnsValue := true, locals := [],
    code := prefixCode narrow signed scalarFirst reversed ++ [.call callee 2] ++ suffix negate }

def Prefix {α : Type} (encode : α → CIL.Value) (widen : α → BitVec 64)
    (program : CIL.Program) (entry pc : Nat) (scalarFirst reversed : Bool) : Prop :=
  ∀ memory input word frame, CallingConditions program memory [input] [] →
    ∀ post : Memory → List Value → Prop,
      (∃ fuel final values, run program fuel entry pc
        (scalarOperatorArguments (scalarFirst != reversed) input (encode word)) frame
        (scalarOperatorArguments scalarFirst input (.i64 (widen word))).reverse memory =
          .ok (final, values) ∧ post final values) →
      ∃ fuel final values, run program fuel entry 0
        (scalarOperatorArguments (scalarFirst != reversed) input (encode word)) frame [] memory =
          .ok (final, values) ∧ post final values

theorem returned (narrow signed scalarFirst reversed negate : Bool) (program : CIL.Program)
    (entry callee : Nat) (found : program[entry]? = some (method narrow signed scalarFirst reversed negate callee))
    (args : List Value) (less : Bool) (frame : Frame) (memory : Memory) :
    run program 3 entry (callPC narrow + 1) args frame
      [.scalar (.i32 (if less then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if less != negate then 1 else 0))]) := by
  have at0 : (method narrow signed scalarFirst reversed negate callee).code[callPC narrow + 1]? =
      some (if negate then .const32 0 else .ret (some .unsigned8)) := by
    cases narrow <;> cases signed <;> cases scalarFirst <;> cases reversed <;> cases negate <;> rfl
  have at1 : (method narrow signed scalarFirst reversed negate callee).code[callPC narrow + 1 + 1]? =
      if negate then some .eq else none := by
    cases narrow <;> cases signed <;> cases scalarFirst <;> cases reversed <;> cases negate <;> rfl
  have at2 : (method narrow signed scalarFirst reversed negate callee).code[callPC narrow + 1 + 1 + 1]? =
      if negate then some (.ret (some .unsigned8)) else none := by
    cases narrow <;> cases signed <;> cases scalarFirst <;> cases reversed <;> cases negate <;> rfl
  have returns : (method narrow signed scalarFirst reversed negate callee).returnsValue = true := rfl
  cases polarity : negate <;> cases less
  all_goals
    simp only [polarity] at found at0 at1 at2 returns
    simp [run, found, at0, at1, at2, step, cil_guard, observerCount, returns,
      pureArity, scalars, CIL.step, CIL.binary, CIL.NarrowKind.extend,
      instruction, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem checked {α : Type} (encode : α → CIL.Value) (widen : α → BitVec 64)
    (narrow signed leafSigned scalarFirst reversed negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (method narrow signed scalarFirst reversed negate callee))
    (leafFound : program[callee]? = some (PrimitiveLeaf.method leafSigned scalarFirst))
    (numeric : ∀ word, numericValue (encode word) = true)
    (prefixTrace : Prefix encode widen program entry (callPC narrow) scalarFirst reversed) :
    ScalarOperatorContract (scalarFirst != reversed) negate encode
      (fun input word => predicate leafSigned scalarFirst input (widen word)) program entry := by
  intro memory input word call
  let body := method narrow signed scalarFirst reversed negate callee
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  have setup : enterFrame body (scalarOperatorArguments (scalarFirst != reversed) input (encode word)) memory =
      .ok (frame, memory) := by
    simp [enterFrame, body, method, makeSelectedLocals, makeLocals, makeArgumentHomes, makeParameterHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have formed := call.input_formed (reference := input) (by simp)
  have checked : (scalarOperatorArguments (scalarFirst != reversed) input (encode word)).mapM (checkedValue memory) =
      .ok (scalarOperatorArguments (scalarFirst != reversed) input (encode word)) := by
    cases scalarFirst <;> cases reversed <;>
      simp [scalarOperatorArguments, scalarArguments, checkedValue, numeric, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨childFuel, final, certificate, cells⟩ :=
    PrimitiveLeaf.checked_template leafSigned scalarFirst program callee leafFound memory input (widen word) call
  have positive (flag : Bool) : (flag != false) = flag := by cases flag <;> rfl
  simp only [positive] at certificate
  have fetched : body.code[callPC narrow]? = some (.call callee 2) := by
    cases narrow <;> cases signed <;> cases scalarFirst <;> cases reversed <;> rfl
  have stepped : step body (.call callee 2) (callPC narrow)
      (scalarOperatorArguments (scalarFirst != reversed) input (encode word)) frame
      (scalarOperatorArguments scalarFirst input (.i64 (widen word))).reverse memory =
      .ok (.call callee (scalarOperatorArguments scalarFirst input (.i64 (widen word))) [] memory) := by
    cases scalarFirst <;>
      simp [step, cil_guard, observerCount, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩
    ⟨3, returned narrow signed scalarFirst reversed negate program entry callee found _ _ frame final⟩
  let post : Memory → List Value → Prop := fun result values => result = leaveFrame frame final ∧
    values = [.scalar (.i32 (if predicate leafSigned scalarFirst (inputValue memory input) (widen word)
      != negate then 1 else 0))]
  obtain ⟨fuel, result, values, finished, sameMemory, sameValues⟩ :=
    prefixTrace memory input word frame call post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst result
  subst values
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  simpa only [leaveFrame, frame, List.foldl_nil] using cells

#print axioms returned
#print axioms checked
end UInt256Proof.Compare.PrimitiveWrapper
