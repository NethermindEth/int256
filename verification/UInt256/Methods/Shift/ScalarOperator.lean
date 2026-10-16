import UInt256.Methods.Shift.ScalarWrapper
import UInt256.Methods.Bitwise.ReturnSetup
import UInt256.Safety.ReadOnlyScalarContract

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

def operatorBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32],
    code := [.arg 0, .arg 1, .localAddr 0, .call callee 3, .local 0, .ret] }

theorem operator_prefix (profile : CIL.FeatureProfile) (callee : Nat)
    (program : CIL.Program) (index fuel : Nat)
    (found : program[index]? = some (operatorBody profile callee))
    (original entered : Memory) (input output : Reference) (count : BitVec 32)
    (call : CallingConditions program entered [input] [output]) :
    run program (fuel + 3) index 0 (scalarArguments input (.i32 count))
        (UInt256Proof.Bitwise.ReturnSafety.frame original output) [] entered =
      run program fuel index 3 (scalarArguments input (.i32 count))
        (UInt256Proof.Bitwise.ReturnSafety.frame original output)
        (shiftArguments input count output).reverse entered := by
  have hl := call.input_formed (reference := input) (by simp)
  have ho := call.output_formed (reference := output) (by simp)
  iterate 3
    apply Eq.trans
    · apply run_next found (by rfl)
      simp (config := { implicitDefEqProofs := false }) only [step, scalarArguments,
        UInt256Proof.Bitwise.ReturnSafety.frame, List.getElem?_cons_zero, List.getElem?_cons_succ,
        checkedValue, numericValue, formValue, localAddress, hl, ho, checkedAt, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      rfl
  rfl

/-- The operator returns aggregate bytes for the mathematical result and retires its private output. -/
theorem operator_correctness (profile : CIL.FeatureProfile) (direction : Direction)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (operatorBody profile callee))
    (child : ShiftContract direction program callee) :
    ReadOnlyScalarContract CIL.Value.i32
      (fun input count => .aggregate (numberBytes (result direction input count).toNat 32)) program index := by
  intro memory input count call
  obtain ⟨output, entered, entry, childCall, before, fresh⟩ := UInt256Proof.Bitwise.ReturnSafety.setup
    (operatorBody profile callee) (scalarArguments input (.i32 count)) rfl rfl rfl rfl program memory [input] call
  obtain ⟨childFuel, childResult, childCert, value, _, ⟨snapshot, loaded⟩, outside⟩ :=
    child entered input count output childCall
  let frame := UInt256Proof.Bitwise.ReturnSafety.frame memory output
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
      (by intro owned member; simp only [frame, UInt256Proof.Bitwise.ReturnSafety.frame, List.mem_singleton] at member
          rw [member, fresh]; exact Nat.le_refl _)
    have growth := (enterFrame_fresh _ _ _ _ _ entry).1.next
    exact (after.cells id bound offset).trans ((outside id (Nat.lt_of_lt_of_le bound growth) offset
      (Or.inl (by rw [fresh]; exact Nat.ne_of_lt bound))).trans (before.cells id bound offset))

#print axioms operator_correctness
#print axioms operator_prefix
end UInt256Proof.Shift.Safety
