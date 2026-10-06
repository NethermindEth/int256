import UInt256.Methods.Shift.ReturnSafetySetup
import UInt256.Methods.Shift.ContextWrapperSafety
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- The operator returns the initialized private result of the actual shift
    wrapper, preserving every pre-existing caller byte. -/
theorem checked_return_contract : ReadOnlyScalarContract CIL.Value.i32
    (fun initial count => .v256 (result shiftDirection initial count))
    Extracted.program Extracted.entryIndex := by
  intro memory input count call
  obtain ⟨frame, entered, temporary, setup, slots, fresh, enteredCall, before⟩ :=
    return_setup memory input count call
  obtain ⟨inputAllocation, inputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.input_formed (by simp : input ∈ [input]))
  have separate : input.allocation ≠ temporary.allocation :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (call.1.1.1 _ _ inputPresent).1 fresh)
  obtain ⟨fuel, final, certificate, value, _, ⟨snapshot, loaded⟩, outside⟩ :=
    checked_wrapper_context entered input count temporary enteredCall (Or.inr separate)
  let expected := result shiftDirection (inputValue entered input) count
  have slot : frame.locals[0]? = some (.bytes .vector256 temporary) := by simp [slots]
  have fi := enteredCall.input_formed (reference := input) (by simp)
  have fo := enteredCall.output_formed (reference := temporary) (by simp)
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by rfl
  have fetched : Extracted.entryBody.code[3]? = some (.call wrapperIndex 3) := by rfl
  have stepped : step Extracted.entryBody (.call wrapperIndex 3) 3
      (scalarArguments input (.i32 count)) frame (shiftArguments input count temporary).reverse entered =
      .ok (.call wrapperIndex (shiftArguments input count temporary) [] entered) := by
    simp [step, shiftArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have decoded : BitVec.ofNat 256 (CIL.Safety.byteNumber snapshot) = expected :=
    (output_snapshot_value final temporary snapshot loaded).trans value
  have localRead : loadLocal final (.bytes .vector256 temporary) = .ok (.scalar (.v256 expected)) := by
    simp [loadLocal, localWidth, loaded, decoded, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run Extracted.program 2 Extracted.entryIndex 4
      (scalarArguments input (.i32 count)) frame [] final =
      .ok (leaveFrame frame final, [.scalar (.v256 expected)]) := by
    apply Eq.trans
    · apply run_next found (by rfl)
      simp [step, slot, localRead, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp [run, cil_code, step, checkedValue, numericValue, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨fuel, certificate.1⟩ ⟨2, tail⟩
  have finished : run Extracted.program (tailFuel + 3) Extracted.entryIndex 0
      (scalarArguments input (.i32 count)) frame [] entered =
      .ok (leaveFrame frame final, [.scalar (.v256 expected)]) := by
    iterate 3
      apply Eq.trans
      · apply run_next found (by rfl)
        simp (config := { implicitDefEqProofs := false })
          [step, scalarArguments, checkedValue, numericValue, formValue, localAddress, slot, fi, fo,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact tail
  dsimp only [expected] at finished
  rw [call.input_value_after_setup setup (by simp : input ∈ [input])] at finished
  have checked : (scalarArguments input (.i32 count)).mapM (checkedValue memory) =
      .ok (scalarArguments input (.i32 count)) := by
    have fi := call.input_formed (reference := input) (by simp)
    simp [scalarArguments, checkedValue, numericValue, formValue, fi, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨tailFuel + 3, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  have owned := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame final memory.nextIdentity
    (fun id member => (owned.2 id member).1)
  intro id bound offset
  have preserved := outside id (Nat.lt_of_lt_of_le bound owned.1.next) offset
    (Or.inl (Nat.ne_of_lt (Nat.lt_of_lt_of_le bound fresh)))
  exact (after.cells id bound offset).trans (preserved.trans (before.cells id bound offset))

theorem checked_return_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid)
    (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun initial count => .v256 (result shiftDirection initial count))
      (CIL.reprofile Extracted.program profile) Extracted.entryIndex :=
  ReadOnlyScalarContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
    (CIL.storage_profile_agreement Extracted.program (by decide) _ _ same) checked_return_contract

#print axioms checked_return_contract
#print axioms checked_return_family_contract
end UInt256Proof.Shift.Safety
