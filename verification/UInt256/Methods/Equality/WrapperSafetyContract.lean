import Extracted
import UInt256.Safety.ReadOnlyExecution
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

/-- Locate a candidate leaf; its contract must still be supplied by a checked
    execution proof when composing the wrappers. -/
def equalityLeafIndex : Nat := Extracted.program.findIdx fun body =>
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false) &&
  body.code.any (fun op => match op with
    | .field _ | .intrinsic (.vector (.equalsAll 256)) _ | .intrinsic (.vector (.equalsAll 128)) _ => true
    | _ => false)

def wrapperIndex (outer : Bool) : Nat :=
  let inner := Extracted.program.findIdx fun body =>
    body.code.any fun op => match op with | .call callee _ => callee == equalityLeafIndex | _ => false
  if !outer then inner else
    let parent := Extracted.program.findIdx fun body =>
      body.aggregateArgs.isEmpty &&
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
    repeat' first
      | exact continuation
      | (apply run_next_exists post
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [cil_code, readOnlyArguments, step, checkedValue, numericValue, formValue,
               fl, fr, pureArity, scalars, CIL.step, CIL.truth, CIL.FeatureProfile.evaluate,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem wrapper_return (outer : Bool) (args : List Value) (flag : BitVec 32)
    (frame : Frame) (memory : Memory)
    (forwarding : (wrapperBody outer).code[wrapperCall outer + 1]? = some .ret) :
    run Extracted.program 1 (wrapperIndex outer) (wrapperCall outer + 1) args frame
      [.scalar (.i32 flag)] memory = .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have lookup : Extracted.program[wrapperIndex outer]? = some (wrapperBody outer) := by
    cases outer <;> rfl
  have returns : (wrapperBody outer).returnsValue = true := by cases outer <;> rfl
  rw [run]
  simp [lookup, forwarding, step, returns, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms wrapper_prefix
#print axioms wrapper_return

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
    (forwarding : (wrapperBody outer).code[wrapperCall outer + 1]? = some .ret)
    (child : EqualityInvocation (wrapperCallee outer)) :
    EqualityInvocation (wrapperIndex outer) := by
  intro memory left right call
  have lookup : Extracted.program[wrapperIndex outer]? = some (wrapperBody outer) := by
    cases outer <;> rfl
  have fits : FrameSetupFits (wrapperBody outer) (readOnlyArguments [left, right]) := by
    cases outer
    all_goals
      conv in (wrapperBody _) => cbv
      simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.readOnly_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, childFinal, childCertificate, childCells⟩ := child entered left right enteredCall
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fetched : (wrapperBody outer).code[wrapperCall outer]? = some (.call (wrapperCallee outer) 2) := by
    cases outer <;> rfl
  have stepped : step (wrapperBody outer) (.call (wrapperCallee outer) 2) (wrapperCall outer)
      (readOnlyArguments [left, right]) frame [.reference (.address right), .reference (.address left)] entered =
      .ok (.call (wrapperCallee outer) (readOnlyArguments [left, right]) [] entered) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
    ⟨childFuel, childCertificate.1⟩ ⟨1, wrapper_return outer _ _ frame childFinal forwarding⟩
  let flag : BitVec 32 := if inputValue entered left = inputValue entered right then 1 else 0
  let post : Memory → List Value → Prop :=
    fun final values => final = leaveFrame frame childFinal ∧ values = [.scalar (.i32 flag)]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    wrapper_prefix outer left right frame entered enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  have initialFlag : flag = (if inputValue memory left = inputValue memory right then 1 else 0) := by
    simp only [flag, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])]
  rw [initialFlag] at finished
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have leftFormed := call.input_formed (reference := left) (by simp)
    have rightFormed := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, leftFormed, rightFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ lookup checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame childFinal memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((childCells id (Nat.lt_of_lt_of_le bound fresh.1.next) offset).trans (before.cells id bound offset))

theorem equality_readOnly_contract
    (entry : EqualityInvocation Extracted.entryIndex) :
    ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  intro memory inputs arity call
  cases inputs with
  | nil => simp at arity
  | cons left rest =>
    cases rest with
    | nil => simp at arity
    | cons right tail =>
      cases tail with
      | cons _ _ => simp at arity
      | nil =>
        simpa only [List.map_cons, List.map_nil, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] using entry memory left right call

#print axioms equality_readOnly_contract
#print axioms wrapper_checked

end UInt256Proof.Equality.Safety
