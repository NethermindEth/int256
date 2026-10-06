import UInt256.Methods.Bitwise.NotReturnSafetySetup
import UInt256.Safety.UnaryOutput
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Bitwise.NotSafety
open CIL.Safety UInt256Model.Safety

variable (unaryIndex : Nat)
    (child : InitializedUnaryContract (fun input => ~~~input) Extracted.program unaryIndex)
    (fetched : Extracted.entryBody.code[2]? = some (.call unaryIndex 2))

include child fetched

theorem return_checked_for (memory : Memory) (input : Reference)
    (call : CallingConditions Extracted.program memory [input] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program Extracted.entryIndex (readOnlyArguments [input]) memory fuel final
        [.scalar (.v256 (~~~inputValue memory input))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  obtain ⟨frame, entered, temporary, setup, slots, fresh, enteredCall, before⟩ :=
    return_setup memory input call
  obtain ⟨fuel, result, certificate, loaded, _, outside⟩ :=
    child entered input temporary enteredCall
  let value := ~~~(inputValue entered input)
  have slot : frame.locals[0]? = some (.bytes .vector256 temporary) := by simp [slots]
  have fl := enteredCall.input_formed (reference := input) (by simp)
  have fo := enteredCall.output_formed (reference := temporary) (by simp)
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have stepped : step Extracted.entryBody (.call unaryIndex 2) 2 (readOnlyArguments [input]) frame
      (unaryArguments input temporary).reverse entered =
      .ok (.call unaryIndex (unaryArguments input temporary) [] entered) := by
    simp [step, unaryArguments, checkedValue, formValue, fl, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have localRead := load_numeric_local .vector256 (.v256 value) value.toNat rfl loaded
  have tail : run Extracted.program 2 Extracted.entryIndex 3 (readOnlyArguments [input]) frame [] result =
      .ok (leaveFrame frame result, [.scalar (.v256 value)]) := by
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp [step, slot, localRead, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact ⟨rfl, rfl, rfl, rfl⟩
    · simp [run, cil_code, step, checkedValue, numericValue,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨fuel, certificate.1⟩ ⟨2, tail⟩
  have finished : run Extracted.program (tailFuel + 2) Extracted.entryIndex 0
      (readOnlyArguments [input]) frame [] entered =
      .ok (leaveFrame frame result, [.scalar (.v256 value)]) := by
    conv in Extracted.entryIndex => cbv
    iterate 2
      apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, readOnlyArguments, checkedValue, formValue, localAddress, slot, fl, fo,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩)
          done
    exact tail
  dsimp only [value] at finished
  rw [call.input_value_after_setup setup (by simp : input ∈ [input])] at finished
  have checked : (readOnlyArguments [input]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [input]) := by
    have fl := call.input_formed (reference := input) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, fl, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨tailFuel + 2, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  have owned := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame result memory.nextIdentity
    (fun id member => (owned.2 id member).1)
  intro id bound offset
  have preserved := outside id (Nat.lt_of_lt_of_le bound owned.1.next) offset
    (Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le bound fresh)))
  exact (after.cells id bound offset).trans (preserved.trans (before.cells id bound offset))

theorem return_contract_for : ReadOnlyContract
    (fun values => .v256 (~~~(values[0]?.getD 0))) Extracted.program Extracted.entryIndex 1 := by
  intro memory inputs arity call
  cases inputs with
  | nil => simp at arity
  | cons input tail =>
    cases tail with
    | cons _ _ => simp at arity
    | nil =>
      simpa only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.getD_some]
        using return_checked_for unaryIndex child fetched memory input call

#print axioms return_contract_for
#print axioms return_checked_for
end UInt256Proof.Bitwise.NotSafety
