import UInt256.Methods.Multiply.CountCarry
import CIL.Safety.NumericHomes
import CIL.Safety.WordMemory
import CIL.Safety.ReturnMemory
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition

namespace UInt256Proof.Multiply.CountSafety
open CIL.Safety

def body (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [.i64 0], localKinds := [.word64],
    code := [.arg 0, .arg 1, .add, .setLocal 0, .arg 2, .arg 2, .load64,
      .local 0, .arg 0, .ltu, .convI8, .add, .store64, .local 0, .ret] }

/-- The carry counter is a checked read/modify/write of one caller word.
    The returned sum and updated counter have independent arithmetic definitions. -/
theorem count_carry_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile)) (memory : Memory) (a b count : BitVec 64) (output : Reference)
    (wf : memory.WellFormed) (writable : access memory output 8 1 true = .ok ())
    (readable : read memory output 8 1 = .ok (numberBytes count.toNat 8)) :
    ∃ fuel final,
      invoke program fuel index
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] memory =
        .ok (final, [.scalar (.i64 (a + b))]) ∧
      final.WellFormed ∧
      read final output 8 1 = .ok (numberBytes (countCarry a b count).toNat 8) ∧
      AccessBelow memory.nextIdentity memory final ∧
      (∀ id, id < memory.nextIdentity → ∀ offset,
        id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
        final.cells id offset = memory.cells id offset) := by
  let args := [Value.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
  let specs : List NumericLocalSpec := [⟨.word64, .i64 0, 0, rfl⟩]
  have formed := access_reference_valid _ _ _ _ _ writable
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ formed
  have old := (wf.1 _ _ present).1
  obtain ⟨frame, entered, setup, homes, before, enteredWF⟩ :=
    numeric_frame_setup (body profile) specs (by rfl) (by rfl) (by rfl) (by rfl) memory args wf
  obtain ⟨home, slot, bound, _, ready⟩ := homes.home_at 0 ⟨.word64, .i64 0, 0, rfl⟩ (by rfl)
  obtain ⟨middle, stored, written, sumRead⟩ := step_store_numeric_local
    (body := (body profile)) (pc := 3) (args := args) (rest := [])
    .word64 (.i64 (a + b)) (a + b).toNat rfl slot ready
  have preserved := before.trans (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have middleWF := write_preserves_wellFormed _ _ _ _ _ enteredWF written
  have readyOutput : access middle output 8 1 true = .ok () :=
    (preserved.access output old 8 1 true).trans writable
  have countRead : read middle output 8 1 = .ok (numberBytes count.toNat 8) :=
    (preserved.read output old 8 1).trans readable
  have formedOutput := access_reference_valid _ _ _ _ _ readyOutput
  have length : (numberBytes (countCarry a b count).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨updated, outputWritten⟩ := write_succeeds
    (bytes := numberBytes (countCarry a b count).toNat 8)
    (by simpa only [length] using readyOutput)
  have outputRead := write_readback _ _ _ _ _ outputWritten
  rw [length] at outputRead
  have retainedSum := write_preserves_disjoint_read outputWritten sumRead
    (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le old bound)))
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retired := leaveFrame_preserves_memory_below frame updated memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  refine ⟨15, leaveFrame frame updated, ?_,
    leaveFrame_preserves_wellFormed _ _ (write_preserves_wellFormed _ _ _ _ _ middleWF outputWritten),
    (retired.read output old 8 1).trans outputRead,
    preserved.accessBelow.trans ((write_preserves_access_below outputWritten _).trans retired.accessBelow), ?_⟩
  · have checked : args.mapM (checkedValue memory) = .ok args := by
      simp [args, checkedValue, numericValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    change invoke program 15 index args memory = _
    simp only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
    have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := (body profile)) (args := args) (pc := pc) (stack := stack)
      .word64 (.i64 (a + b)) (a + b).toNat rfl slot sumRead
    have loadRetained := step_load_numeric_local (body := (body profile))
      (args := args) (pc := 13) (stack := []) .word64 (.i64 (a + b)) (a + b).toNat rfl slot retainedSum
    have loadCount := load_word64_of_read countRead
    have storedOutput : step (body profile) .store64 12 args frame
        [.scalar (.i64 (countCarry a b count)), .reference (.address output)] middle =
        .ok (.next 13 [] frame updated) := by
      simp only [step, pureArity, instruction, storeValue, referenceAt, outputWritten, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    iterate 12
      apply Eq.trans
      · apply run_next found (by rfl)
        first
        | exact stored
        | exact loadSum _ _
        | rfl
        | simp (config := { implicitDefEqProofs := false })
            [step, args, checkedValue, formValue, formedOutput, checkedAt,
              pureArity, instruction, loadCount,
              Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    have flag : (BitVec.signExtend 64 (if a + b < a then BitVec.ofNat 32 1 else BitVec.ofNat 32 0)) = sumHigh a b := by
      rw [← sumHigh_flag]
      split <;> rfl
    apply Eq.trans
    · apply run_next found (by rfl)
      simpa [countCarry, ← flag, localResult] using storedOutput
    apply Eq.trans
    · exact run_next found (by rfl) loadRetained
    rw [run]
    have fetched : (body profile).code[14]? = some .ret := by rfl
    simp only [found, fetched]
    rfl
  · intro id bound offset outside
    rw [retired.cells id bound offset]
    exact (write_outside _ _ _ _ _ id offset outputWritten
      (by simpa only [length] using outside)).trans (preserved.cells id bound offset)

#print axioms count_carry_invoke
end UInt256Proof.Multiply.CountSafety
