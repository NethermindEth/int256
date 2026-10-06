import UInt256.Methods.Compare.PrimitiveSafetyContract
import UInt256.Safety.ScalarValueContract
import UInt256.Safety.ArgumentValues
import CIL.Safety.CallComposition
import CIL.Safety.NegationReturn

namespace UInt256Proof.Compare.PrimitiveValueSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

theorem value_setup (memory : Memory) (word : BitVec 64) (input : BitVec 256)
    (call : CallingConditions Extracted.program memory [] []) :
    ∃ frame entered copy,
      enterFrame Extracted.entryBody (scalarValueArguments (.i64 word) input) memory = .ok (frame, entered) ∧
      argumentHome frame 1 = .ok (.bytes .vector256 copy) ∧
      CallingConditions Extracted.program entered [copy] [] ∧
      inputValue entered copy = input := by
  obtain ⟨copy, entered, made, loaded, _, _⟩ :=
    make_argument_home256 memory memory.nextIdentity 1 (scalarValueArguments (.i64 word) input)
      input call.1.1 rfl
  let frame : Frame := {
    activation := memory.nextIdentity, locals := [], owned := [copy.allocation],
    arguments := [(1, .bytes .vector256 copy)] }
  have setup : enterFrame Extracted.entryBody (scalarValueArguments (.i64 word) input) memory =
      .ok (frame, entered) := by
    simp [enterFrame, cil_code, makeLocals, made, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨frame, entered, copy, setup, ?_,
    (call.after_frame_setup setup).with_readable_input loaded, inputValue_of_encoded_read loaded⟩
  simp [argumentHome, frame, Pure.pure, Except.pure]

theorem value_prefix (memory : Memory) (word : BitVec 64) (input : BitVec 256)
    (copy : Reference) (frame : Frame)
    (home : argumentHome frame 1 = .ok (.bytes .vector256 copy))
    (call : CallingConditions Extracted.program memory [copy] [])
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex 2 (scalarValueArguments (.i64 word) input) frame
        [.scalar (.i64 word), .reference (.address copy)] memory = .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex 0 (scalarValueArguments (.i64 word) input) frame [] memory =
        .ok (final, values) ∧ post final values := by
  have formed := call.input_formed (reference := copy) (by simp)
  iterate 2
    apply run_next_exists post
    · simp only [cil_code]; rfl
    · simp only [cil_code]; rfl
    · simp [step, scalarValueArguments, home, localAddress, checkedValue, numericValue, formValue,
        formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation

theorem checked_contract : ScalarValueContract CIL.Value.i64
    (fun word input => .i32 (if word.toNat ≤ input.toNat then 1 else 0))
    Extracted.program Extracted.entryIndex := by
  intro memory word input call
  obtain ⟨frame, entered, copy, setup, home, enteredCall, copyValue⟩ := value_setup memory word input call
  have found : Extracted.program[Extracted.entryIndex]? = some Extracted.entryBody := by simp only [cil_code]
  have checked : (scalarValueArguments (.i64 word) input).mapM (checkedValue memory) =
      .ok (scalarValueArguments (.i64 word) input) := by
    simp [scalarValueArguments, checkedValue, numericValue, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  obtain ⟨childFuel, childFinal, certificate, cells⟩ := leaf_checked entered copy word enteredCall
  have positive (flag : Bool) : (flag != false) = flag := by cases flag <;> rfl
  simp only [positive, show leafScalarFirst = false from rfl, show leafSigned = false from rfl,
    predicate, Bool.false_eq_true, ite_false, copyValue] at certificate
  have formed := enteredCall.input_formed (reference := copy) (by simp)
  have fetched : Extracted.entryBody.code[2]? = some (.call leafIndex 2) := by rfl
  have stepped : step Extracted.entryBody (.call leafIndex 2) 2 (scalarValueArguments (.i64 word) input)
      frame [.scalar (.i64 word), .reference (.address copy)] entered =
      .ok (.call leafIndex (scalarOperatorArguments false copy (.i64 word)) [] entered) := by
    simp [step, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned := run_negation_return Extracted.program Extracted.entryIndex 3 Extracted.entryBody
    found (by rfl) (by rfl) (by rfl) (by rfl) (scalarValueArguments (.i64 word) input) frame childFinal
    (if decide ((input.toNat : Int) < (word.toNat : Int)) then 1 else 0)
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩ ⟨3, returned⟩
  have result : (if (if decide ((input.toNat : Int) < (word.toNat : Int)) then (1 : BitVec 32) else 0) = 0
      then (1 : BitVec 32) else 0) = (if word.toNat ≤ input.toNat then 1 else 0) := by
    by_cases ordered : word.toNat ≤ input.toNat
    · have opposite : ¬ (input.toNat : Int) < (word.toNat : Int) := by omega
      simp [ordered, opposite]
    · have opposite : (input.toNat : Int) < (word.toNat : Int) := by omega
      simp [ordered, opposite]
  rw [result] at tail
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame childFinal ∧ values = [.scalar (.i32 (if word.toNat ≤ input.toNat then 1 else 0))]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    value_prefix entered word input copy frame home enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame childFinal memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((cells id (Nat.lt_of_lt_of_le bound fresh.1.next) offset).trans (before.cells id bound offset))

#print axioms value_setup
#print axioms value_prefix
#print axioms checked_contract
end UInt256Proof.Compare.PrimitiveValueSafety
