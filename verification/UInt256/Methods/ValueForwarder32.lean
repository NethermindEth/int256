import UInt256.Safety.StepEquation
import UInt256.Safety.ReadOnlyContract
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory
import UInt256.Safety.ParameterSetup32
import UInt256.Safety.ReadOnlyScalarContract

namespace UInt256Proof.ValueForwarder32
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (booleanReturn : Bool) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], parameterHomes := [(1, .aggregate 32)],
    code := [.arg 0, .localAddr 0, .call callee 2, .ret (if booleanReturn then some .unsigned8 else none)] }

def encode (value : BitVec 256) : CIL.Value := .aggregate (numberBytes value.toNat 32)

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (booleanReturn : Bool) (operation : BitVec 256 → BitVec 256 → BitVec 32)
    (range : ∀ left right, booleanReturn = true → operation left right = 0 ∨ operation left right = 1)
    (found : program[index]? = some (body profile booleanReturn callee))
    (child : ∀ memory left right, CallingConditions program memory [left, right] [] →
      ∃ fuel final,
        InvocationCertificate program callee (readOnlyArguments [left, right]) memory fuel final
          [.scalar (.i32 (operation (inputValue memory left) (inputValue memory right)))] ∧
        ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset) :
    ReadOnlyScalarContract encode (fun left right => .i32 (operation left right)) program index := by
  intro memory left right call
  obtain ⟨copy, entered, setup, enteredCall, copyValue, before, fresh⟩ :=
    parameter_setup32 (body profile booleanReturn callee) (scalarArguments left (encode right)) right
      rfl rfl rfl rfl rfl program memory [left] call
  let frame := parameterFrame32 memory copy
  have formed := call.input_formed (reference := left) (by simp)
  have checked : (scalarArguments left (encode right)).mapM (checkedValue memory) =
      .ok (scalarArguments left (encode right)) := by
    simp [scalarArguments, encode, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fc := enteredCall.input_formed (reference := copy) (by simp)
  have leftValue := call.input_value_after_setup setup (by simp : left ∈ [left])
  obtain ⟨childFuel, final, certificate, cells⟩ :=
    child entered left copy enteredCall
  have returnTrace : run program 1 index 3 (scalarArguments left (encode right)) frame
      [.scalar (.i32 (operation (inputValue entered left) (inputValue entered copy)))] final =
      .ok (leaveFrame frame final, [.scalar (.i32 (operation (inputValue entered left) (inputValue entered copy)))]) := by
    cases mode : booleanReturn
    · simp [run, found, body, mode, step, checkedValue, numericValue,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rcases range (inputValue entered left) (inputValue entered copy) mode with flag | flag <;>
        simp [run, found, body, mode, step, checkedValue, numericValue, CIL.NarrowKind.extend, flag,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step (body profile booleanReturn callee) (.call callee 2) 2
      (scalarArguments left (encode right)) frame
      [.reference (.address copy), .reference (.address left)] entered =
      .ok (.call callee (readOnlyArguments [left, copy]) [] entered) := by
    simp [step, readOnlyArguments, checkedValue, formValue, fl, fc, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, certificate.1⟩ ⟨1, returnTrace⟩
  have executed : run program (tailFuel + 2) index 0 (scalarArguments left (encode right)) frame [] entered =
      .ok (leaveFrame frame final, [.scalar (.i32 (operation (inputValue entered left) (inputValue entered copy)))]) := by
    iterate 2
      apply Eq.trans
      · apply run_next found
        · simp only [body]; rfl
        · simp (config := { implicitDefEqProofs := false }) [step, scalarArguments, checkedValue, formValue, fl, fc,
            localAddress, frame, parameterFrame32, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact ⟨rfl, rfl, rfl, rfl⟩
    exact tail
  rw [leftValue, copyValue] at executed
  refine ⟨tailFuel + 2, leaveFrame frame final,
    certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live executed, ?_⟩
  have privateFrame : frame.OwnedAbove memory.nextIdentity := by
    intro id member
    simp only [frame, parameterFrame32, List.mem_singleton] at member
    subst id
    exact Nat.le_of_eq fresh.symm
  have after := leaveFrame_preserves_memory_below frame final memory.nextIdentity privateFrame
  have growth : memory.nextIdentity < entered.nextIdentity := by
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ fc
    rw [← fresh]
    exact (enteredCall.1.1.1 _ _ present).1
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((cells id (Nat.lt_trans bound growth) offset).trans (before.cells id bound offset))

#print axioms checked
end UInt256Proof.ValueForwarder32
