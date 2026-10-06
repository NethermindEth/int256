import UInt256.Methods.Shift.SafetyCountStores
import UInt256.Safety.LimbAccess

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Each actual operand load saves an initial-input limb into a private home.
    Caller-byte preservation permits arbitrary overlap with the future output. -/
theorem shift_operand_save (original entered current : Memory)
    (inputs outputs : List Reference) (input : Reference) (frame : Frame) (args : List Value)
    (index : Fin 4) (argument : args[0]? = some (.reference (.address input)))
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs) (member : input ∈ inputs)
    (inputSame : ∀ offset, current.cells input.allocation offset = original.cells input.allocation offset)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[3 + index.val]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes (inputLimb original input index).toNat 8) →
      MemoryBelow original.nextIdentity current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (inputLimb original input index).toNat 8) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc (30 + 3 * index.val)) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc (27 + 3 * index.val)) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have spec : shiftSpecs[3 + index.val]? = some ⟨.word64, .i64 0, 0, rfl⟩ := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨reference, after, slot, loaded, kept, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store Extracted.program shiftBody shiftSpecs original.nextIdentity entered current
      inputs outputs frame currentCall enteredWF homes authority (3 + index.val) _ spec
      (.i64 (inputLimb original input index)) (inputLimb original input index).toNat rfl
  have done := continuation reference after slot loaded kept afterCall afterAuthority written
  have formed := currentCall.input_formed member
  have reading (rest : List Value) : instruction (.field index) (.reference (.address input) :: rest) current =
      .ok (current, .scalar (.i64 (inputLimb original input index)) :: rest) := by
    rw [currentCall.input_field_instruction member index rest]
    simp only [inputLimb, inputSame]
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    dsimp at reading stored done
    iterate 2
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, argument, checkedValue, numericValue, formValue, formed, reading,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists post found (by rfl) (stored _ _ _)
    exact done

#print axioms shift_operand_save
end UInt256Proof.Shift.Safety
