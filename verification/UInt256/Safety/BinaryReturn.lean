import UInt256.Safety.BinaryReturnSetup
import UInt256.Safety.InitializedOutput
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory

namespace UInt256Model.Safety
open CIL.Safety UInt256Model.Safety

variable (program : CIL.Program) (entry : Nat) (body : CIL.Method)
    (operation : BitVec 256 → BitVec 256 → BitVec 256) (binaryIndex : Nat)
    (child : InitializedBinaryContract operation program binaryIndex)
    (found : program[entry]? = some body)
    (code : body.code = [.arg 0, .arg 1, .aggregateLocalAddr 0, .call binaryIndex 3,
      .aggregateLocal 0, .ret])
    (kinds : body.localKinds = numericKinds binaryResultSpecs)
    (values : body.locals = numericInitializers binaryResultSpecs)
    (arguments : body.aggregateArgs = []) (returns : body.returnsValue = true)

include child found code kinds values arguments returns

theorem binary_return_checked : BinaryReadOnlyInvocation
    (fun left right => .v256 (operation left right))
    program entry := by
  intro memory left right call
  obtain ⟨frame, entered, temporary, setup, slots, fresh, enteredCall, before⟩ :=
    binary_return_setup program body kinds values arguments memory left right call
  obtain ⟨fuel, result, certificate, loaded, _, outside⟩ :=
    child entered left right temporary enteredCall
  let value := operation (inputValue entered left) (inputValue entered right)
  have slot : frame.locals[0]? = some (.bytes .vector256 temporary) := by simp [slots]
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := temporary) (by simp)
  have fetched : body.code[3]? = some (.call binaryIndex 3) := by rw [code]; rfl
  have stepped : step body (.call binaryIndex 3) 3 (readOnlyArguments [left, right]) frame
      (binaryArguments left right temporary).reverse entered =
      .ok (.call binaryIndex (binaryArguments left right temporary) [] entered) := by
    simp [step, binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have localRead := load_numeric_local .vector256 (.v256 value) value.toNat rfl loaded
  have tail : run program 2 entry 4 (readOnlyArguments [left, right]) frame [] result =
      .ok (leaveFrame frame result, [.scalar (.v256 value)]) := by
    apply Eq.trans
    · apply run_next
      · first | exact found | (rw [code]; rfl)
      · first | exact found | (rw [code]; rfl)
      · simp [step, slot, localRead, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact ⟨rfl, rfl, rfl, rfl⟩
    · simp [run, found, code, returns, step, checkedValue, numericValue, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨fuel, certificate.1⟩ ⟨2, tail⟩
  have finished : run program (tailFuel + 3) entry 0
      (readOnlyArguments [left, right]) frame [] entered =
      .ok (leaveFrame frame result, [.scalar (.v256 value)]) := by
    iterate 3
      apply Eq.trans
      · apply run_next
        · first | exact found | (rw [code]; rfl)
        · first | exact found | (rw [code]; rfl)
        · simp (config := { implicitDefEqProofs := false })
            [step, readOnlyArguments, checkedValue, formValue, localAddress, slot, fl, fr, fo,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩)
          done
    exact tail
  dsimp only [value] at finished
  rw [call.input_value_after_setup setup (by simp : left ∈ [left, right]),
    call.input_value_after_setup setup (by simp : right ∈ [left, right])] at finished
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨tailFuel + 3, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  have owned := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame result memory.nextIdentity
    (fun id member => (owned.2 id member).1)
  intro id bound offset
  have preserved := outside id (Nat.lt_of_lt_of_le bound owned.1.next) offset
    (Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le bound fresh)))
  exact (after.cells id bound offset).trans (preserved.trans (before.cells id bound offset))

theorem binary_return_contract : ReadOnlyContract
    (fun values => .v256 (operation
      (values[0]?.getD 0) (values[1]?.getD 0))) program entry 2 := by
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
          List.getElem?_cons_succ, Option.getD_some] using binary_return_checked program entry body operation binaryIndex child found code kinds values arguments returns memory left right call

#print axioms binary_return_contract
#print axioms binary_return_checked
end UInt256Model.Safety
