import UInt256.Methods.Shift.ScalarOperator
import UInt256.Safety.AggregateReturn

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- The shift contract restricted to outputs in a different allocation from the input. -/
def DisjointShiftContract (direction : Direction) (program : CIL.Program) (entry : Nat) : Prop :=
  ∀ (memory : Memory) (input : Reference) (count : BitVec 32) (output : Reference),
    CallingConditions program memory [input] [output] → output.allocation ≠ input.allocation →
    ShiftInvocation direction program entry memory input count output
theorem operator_disjoint_correctness (profile : CIL.FeatureProfile) (direction : Direction)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (operatorBody profile callee))
    (child : DisjointShiftContract direction program callee) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun input count => .aggregate (numberBytes (result direction input count).toNat 32)) program index := by
  intro memory input count call
  obtain ⟨output, entered, entry, childCall, before, fresh⟩ := UInt256Model.Safety.AggregateReturn.setup
    (operatorBody profile callee) (scalarArguments input (.i32 count)) rfl rfl rfl rfl program memory [input] call
  obtain ⟨childFuel, childResult, childCert, value, _, ⟨snapshot, loaded⟩, outside⟩ :=
    child entered input count output childCall (AggregateReturn.fresh_disjoint call fresh input (by simp))
  let frame := UInt256Model.Safety.AggregateReturn.frame memory output
  let args := scalarArguments input (.i32 count)
  let bits := result direction (inputValue entered input) count
  let bytes := numberBytes bits.toNat 32
  have length : snapshot.length = 32 := by rw [read_result_snapshot loaded]; simp
  have number := output_snapshot_value childResult output snapshot loaded
  rw [value] at number
  have encoded : bytes = snapshot := by
    dsimp [bytes, bits]
    rw [← number]
    exact vector256_bytes_roundtrip snapshot length
  have readback : read childResult output 32 1 = .ok bytes := by rw [encoded]; exact loaded
  have hl := childCall.input_formed (reference := input) (by simp)
  have ho := childCall.output_formed (reference := output) (by simp)
  have stepped : step (operatorBody profile callee) (.call callee 3) 3 args frame
      (shiftArguments input count output).reverse entered =
      .ok (.call callee (shiftArguments input count output) [] entered) := by
    simp [step, shiftArguments, checkedValue, numericValue, formValue, hl, ho, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run program 2 index 4 args frame [] childResult =
      .ok (leaveFrame frame childResult, [.scalar (.aggregate bytes)]) := by
    apply Eq.trans
    · apply run_next (target := 5) (values := [.scalar (.aggregate bytes)])
        (nextFrame := frame) (updated := childResult) found (by rfl)
      exact step_load_aggregate (size := 32) (reference := output) (by rfl) readback
    · apply run_return found (by rfl) (by rfl) (by rfl)
  obtain ⟨fuel, finish⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, childCert.1⟩ ⟨2, tail⟩
  have executed := (operator_prefix profile callee program index fuel found memory entered input output count childCall).trans finish
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, scalarArguments, checkedValue, numericValue, formValue, call.input_formed (by simp : input ∈ [input]),
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked entry
  refine ⟨fuel + 3, leaveFrame frame childResult, ?_, ?_⟩
  · have certificate := certify_invocation _ _ _ _ _ _ _ _ _ _ found checked entry live executed
    simpa only [bytes, bits, call.input_value_after_setup entry (by simp : input ∈ [input])] using certificate
  · intro id bound offset
    have after := leaveFrame_preserves_memory_below frame childResult memory.nextIdentity
      (by intro owned member; simp only [frame, UInt256Model.Safety.AggregateReturn.frame, List.mem_singleton] at member
          rw [member, fresh]; exact Nat.le_refl _)
    have growth := (enterFrame_fresh _ _ _ _ _ entry).1.next
    exact (after.cells id bound offset).trans ((outside id (Nat.lt_of_lt_of_le bound growth) offset
      (Or.inl (by rw [fresh]; exact Nat.ne_of_lt bound))).trans (before.cells id bound offset))

#print axioms operator_disjoint_correctness

theorem wrapper_disjoint_correctness (profile : CIL.FeatureProfile) (direction : Direction)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (wrapperBody profile callee))
    (child : DisjointShiftContract direction program callee) : DisjointShiftContract direction program index := by
  intro memory input count output call disjoint
  obtain ⟨childFuel, final, certificate, value, writable, readable, outside⟩ :=
    child memory input count output call disjoint
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  let args := shiftArguments input count output
  have fi := call.input_formed (by simp : input ∈ [input])
  have fo := call.output_formed (by simp : output ∈ [output])
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, shiftArguments, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (wrapperBody profile callee) args memory = .ok (frame, memory) := rfl
  have stepped : step (wrapperBody profile callee) (.call callee 3) 3 args frame args.reverse memory =
      .ok (.call callee args [] memory) := by
    simp [args, shiftArguments, step, checkedValue, numericValue, formValue, fi, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run program 1 index 4 args frame [] final = .ok (final, []) :=
    run_return found (by rfl) (by rfl) (by rfl)
  obtain ⟨fuel, finished⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, certificate.1⟩ ⟨1, tail⟩
  have leading : run program (fuel + 3) index 0 args frame [] memory =
      run program fuel index 3 args frame args.reverse memory := by
    iterate 3
      apply Eq.trans
      · apply run_next found (by rfl)
        simp (config := { implicitDefEqProofs := false }) [step, args, shiftArguments,
          checkedValue, numericValue, formValue, fi, fo, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    rfl
  exact ⟨fuel + 3, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup
    (checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup) (leading.trans finished),
    value, writable, readable, outside⟩


#print axioms wrapper_disjoint_correctness
end UInt256Proof.Shift.Safety
