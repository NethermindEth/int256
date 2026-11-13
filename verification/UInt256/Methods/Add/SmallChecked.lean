import UInt256.Methods.Add.SmallFinish
import UInt256.Safety.InputWords
import UInt256.Methods.Reporting.Arithmetic
import CIL.Safety.LocalSnapshotSteps

/-! Checked execution of the extracted small-addition helper on every carry path. -/

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

def smallOverflow (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference)
    (word : BitVec 64) : BitVec 32 :=
  if 2^256 ≤ (inputValue memory input).toNat + word.toNat then 1 else 0

theorem smallOverflow_cases (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference)
    (word : BitVec 64) :
    smallOverflow memory input word =
      if inputLimb memory input 0 + word < inputLimb memory input 0 ∧
        inputLimb memory input 1 + 1 = 0 ∧ inputLimb memory input 2 + 1 = 0 ∧
        inputLimb memory input 3 + 1 = 0 then 1 else 0 := by
  have overflow := UInt256Proof.Reporting.small_overflow_iff (inputLimb memory input) word
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits)
      input.offset
  have wideBound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
  rw [initial] at overflow
  simp [UInt256Model.value, UInt256Proof.singleLimb, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt wideBound] at overflow
  unfold smallOverflow
  simp only [BitVec.ofNat_eq_ofNat, Nat.reducePow, ← overflow]

theorem small_result_value (memory : CIL.Safety.Memory) (input : CIL.Safety.Reference)
    (word : BitVec 64) :
    UInt256Model.value (UInt256Proof.smallResult (inputLimb memory input) word) =
      inputValue memory input + BitVec.ofNat 256 word.toNat := by
  rw [UInt256Proof.small_result_sum]
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits)
      input.offset
  rw [initial]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- State an exit's store call at its numeral pc with its argument stack in call order. -/
local macro "small_exit_stack" " at " done:ident : tactic => `(tactic| (
  unfold storageArguments at $done:ident
  rw [small_storage_word_order] at $done:ident
  conv at $done:ident in (List.filterMap _ _) => cbv
  simp [List.range_succ, List.findIdx] at $done:ident
  conv at $done:ident in (smallStoreCall _) => cbv))

/-- Checked small addition: input snapshots, low sum, every carry exit and the exact result. -/
theorem small_checked (memory : CIL.Safety.Memory) (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarUInt64Index
        (smallArguments input output word) memory = .ok (final, values) ∧
      SmallResult memory final values input output word (smallOverflow memory input word) := by
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    small_frame_setup memory (smallArguments input output word) call.1.1
  have checked : (smallArguments input output word).mapM (checkedValue memory) =
      .ok (smallArguments input output word) := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [smallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  suffices executed : ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (smallArguments input output word) frame [] entered = .ok (final, values) ∧
      SmallResult memory final values input output word (smallOverflow memory input word) by
    obtain ⟨fuel, final, values, finished, result⟩ := executed
    refine ⟨fuel, final, values, ?_, result⟩
    simpa only [invoke, cil_code, checked, setup, Except.mapError, Bind.bind, Except.bind]
      using finished
  have exit (branch : Fin 5) (current : Memory)
      (currentCall : CallingConditions Extracted.program current [input] [output])
      (preserved : MemoryBelow memory.nextIdentity memory current)
      (flag : smallOverflow memory input word = smallBranchFlag branch) :
      ∃ fuel final values,
        run Extracted.program fuel Extracted.addScalarUInt64Index (smallStoreCall branch.val)
          (smallArguments input output word) frame
          (storageArguments output
            (UInt256Proof.smallResult (inputLimb memory input) word 0)
            (UInt256Proof.smallResult (inputLimb memory input) word 1)
            (UInt256Proof.smallResult (inputLimb memory input) word 2)
            (UInt256Proof.smallResult (inputLimb memory input) word 3)).reverse current =
              .ok (final, values) ∧
        SmallResult memory final values input output word (smallOverflow memory input word) := by
    rw [flag]
    exact small_store_finish branch memory entered current frame input output word _ call setup
      currentCall preserved.cells (small_result_value memory input word)
  have enteredCall := call.after_frame_setup setup
  have valid := enteredCall.1
  have world := enteredCall.2
  have enteredFormed := valid.1
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have limbs := fun current below =>
    call.input_words_kept (current := current) below input (by simp)
  cil_contract_steps (snapshots := LocalSnapshots.empty entered frame.locals)
    [smallArguments, limbs _ preserved, CIL.FeatureProfile.evaluate]
  split
  next carry =>
    cil_contract_steps (snapshots := localSnapshots_4) [smallArguments]
    split
    next first =>
      have done := exit 1 storedLocal_5 ⟨valid, by stored_world⟩ preserved
        (by simp [smallOverflow_cases, smallBranchFlag, carry, first])
      small_exit_stack at done
      simp [UInt256Proof.smallResult, carry, first] at done
      cil_contract_steps (snapshots := localSnapshots_5) [smallArguments] until done
    next first =>
      replace first := Decidable.not_not.mp first
      cil_contract_steps (snapshots := localSnapshots_5) [smallArguments]
      split
      next second =>
        have done := exit 2 storedLocal_6 ⟨valid, by stored_world⟩ preserved
          (by simp [smallOverflow_cases, smallBranchFlag, carry, first, second])
        small_exit_stack at done
        simp [UInt256Proof.smallResult, carry, first, second] at done
        cil_contract_steps (snapshots := localSnapshots_6) [smallArguments] until done
      next second =>
        replace second := Decidable.not_not.mp second
        cil_contract_steps (snapshots := localSnapshots_6) [smallArguments]
        split
        next third =>
          have done := exit 3 storedLocal_7 ⟨valid, by stored_world⟩ preserved (by
            simp [smallOverflow_cases, smallBranchFlag, carry, first, second, third,
              show (3 : Fin 5).val = 3 from rfl])
          small_exit_stack at done
          simp [UInt256Proof.smallResult, carry, first, second] at done
          cil_contract_steps (snapshots := localSnapshots_7) [smallArguments] until done
        next third =>
          replace third := Decidable.not_not.mp third
          have done := exit 4 storedLocal_7 ⟨valid, by stored_world⟩ preserved (by
            simp [smallOverflow_cases, smallBranchFlag, carry, first, second, third,
              show (4 : Fin 5).val = 4 from rfl])
          small_exit_stack at done
          simp [UInt256Proof.smallResult, carry, first, second, third] at done
          cil_contract_steps (snapshots := localSnapshots_7) [smallArguments] until done
  next carry =>
    have done := exit 0 storedLocal_4 ⟨valid, by stored_world⟩ preserved
      (by simp [smallOverflow_cases, smallBranchFlag, carry])
    small_exit_stack at done
    simp [UInt256Proof.smallResult, carry] at done
    cil_contract_steps (snapshots := localSnapshots_4) [smallArguments] until done

end UInt256Proof.Safety