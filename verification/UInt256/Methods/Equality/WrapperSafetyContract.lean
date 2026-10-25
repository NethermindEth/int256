import UInt256.Safety.ReadOnlyForwarder
import CIL.Safety.SymbolicExecution
import UInt256.Methods.Bindings
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

/-- Locate a candidate leaf; its contract must still be supplied by a checked
    execution proof when composing the wrappers. -/
def equalityLeafIndex : Nat := Extracted.program.findIdx fun body =>
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false) &&
  body.code.any (fun op => match op with
    | .fieldAt _ _ | .intrinsic (.vector (.equalsAll 256)) _ | .intrinsic (.vector (.equalsAll 128)) _ => true
    | _ => false)

def wrapperIndex (outer : Bool) : Nat :=
  let inner := Extracted.program.findIdx fun body =>
    body.code.any fun op => match op with | .call callee _ => callee == equalityLeafIndex | _ => false
  if !outer then inner else
    let parent := Extracted.program.findIdx fun body =>
      body.parameterHomes.isEmpty &&
      body.code.any fun op => match op with | .call callee _ => callee == inner | _ => false
    if parent < Extracted.program.length then parent else inner

def wrapperBody (outer : Bool) : CIL.Method := Extracted.program[wrapperIndex outer]?.getD
  { code := [], locals := [], returnsValue := false }

def wrapperCall (outer : Bool) : Nat := (wrapperBody outer).code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

theorem wrapper_prefix (outer : Bool) (left right : Reference) (frame : Frame) (memory : Memory)
    (call : CallingConditions Extracted.program memory [left, right] [])
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel (wrapperIndex outer) (wrapperCall outer)
        (readOnlyArguments [left, right]) frame
        [.reference (.address right), .reference (.address left)] memory = .ok (final, values) ∧
      post final values) :
    ∃ fuel final values, run Extracted.program fuel (wrapperIndex outer) 0
      (readOnlyArguments [left, right]) frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  cases outer
  all_goals
    conv in (wrapperIndex _) => cbv
    conv at continuation in (wrapperIndex _) => cbv
    conv at continuation in (wrapperCall _) => cbv
    cil_contract_steps [readOnlyArguments, fl, fr] until continuation

#print axioms wrapper_prefix

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def EqualityInvocation (method : Nat) : Prop :=
  ∀ (memory : Memory) (left right : Reference),
    CallingConditions Extracted.program memory [left, right] [] →
    ∃ fuel final,
      InvocationCertificate Extracted.program method (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

def wrapperCallee (outer : Bool) : Nat :=
  match (wrapperBody outer).code[wrapperCall outer]? with
  | some (.call callee _) => callee
  | _ => Extracted.program.length

theorem wrapper_checked (outer : Bool)
    (forwarding : (wrapperBody outer).code[wrapperCall outer + 1]? = some (.ret (some .unsigned8)))
    (child : EqualityInvocation (wrapperCallee outer)) :
    EqualityInvocation (wrapperIndex outer) := by
  apply forward_readOnly_binary Extracted.program (wrapperIndex outer) (wrapperCall outer)
    (wrapperCallee outer) (wrapperBody outer)
    (fun left right => .i32 (if left = right then 1 else 0))
    (fun left right => readOnlyArguments [left, right])
  · cases outer <;> rfl
  · cases outer <;> rfl
  · exact forwarding
  · cases outer <;> rfl
  · intro left right
    cases outer
    all_goals
      conv in (wrapperBody _) => cbv
      simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit,
        ParameterArgumentsFit, SelectedKindsFit]
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro left right
    refine ⟨_, rfl, ?_⟩
    split <;> decide
  · exact child
  · intro memory left right frame call post continuation
    exact wrapper_prefix outer left right frame memory call post continuation

theorem equality_readOnly_contract
    (entry : EqualityInvocation Extracted.entryIndex) :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  exact BinaryReadOnlyInvocation.to_contract
    (operation := fun left right => .i32 (if left = right then 1 else 0))
    (program := Extracted.program) (method := Extracted.entryIndex) entry

#print axioms equality_readOnly_contract
#print axioms wrapper_checked

end UInt256Proof.Equality.Safety
