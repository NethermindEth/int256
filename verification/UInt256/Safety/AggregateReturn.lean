import UInt256.Safety.UnaryContract
import UInt256.Safety.AggregateReturnSetup
import UInt256.Safety.Contract
import UInt256.Safety.OutputReadability
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory
import CIL.Safety.CallComposition

namespace UInt256Model.Safety.AggregateReturn
open CIL.Safety UInt256Model.Safety

def binaryBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32],
    code := [.arg 0, .arg 1, .localAddr 0, .call callee 3, .local 0, .ret] }

def binaryArgs (left right : Reference) : List Value :=
  [.reference (.address left), .reference (.address right)]

def BinaryContract (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (program : CIL.Program) (index : Nat) : Prop :=
  ∀ memory left right, CallingConditions program memory [left, right] [] →
    ∃ fuel final bytes,
      InvocationCertificate program index (binaryArgs left right) memory fuel final [.scalar (.aggregate bytes)] ∧
      bytes.length = 32 ∧
      BitVec.ofNat 256 (CIL.Safety.byteNumber bytes) = operation (inputValue memory left) (inputValue memory right) ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

theorem binary_prefix (profile : CIL.FeatureProfile) (callee : Nat)
    (program : CIL.Program) (index fuel : Nat)
    (found : program[index]? = some (binaryBody profile callee))
    (original entered : Memory) (left right output : Reference)
    (call : CallingConditions program entered [left, right] [output]) :
    run program (fuel + 3) index 0 (binaryArgs left right) (frame original output) [] entered =
      run program fuel index 3 (binaryArgs left right) (frame original output)
        (binaryArguments left right output).reverse entered := by
  have hl := call.input_formed (reference := left) (by simp)
  have hr := call.input_formed (reference := right) (by simp)
  have ho := call.output_formed (reference := output) (by simp)
  iterate 3
    apply Eq.trans
    · apply run_next found
      · simp only [binaryBody]; rfl
      · simp (config := { implicitDefEqProofs := false }) only [step, binaryArgs, frame, List.getElem?_cons_zero, List.getElem?_cons_succ,
          checkedValue, formValue, localAddress, hl, hr, ho, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        rfl
  rfl

def InitializedBinaryResult (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (program : CIL.Program) (index : Nat) : Prop :=
  ∀ memory left right output, CallingConditions program memory [left, right] [output] →
    ∃ fuel final, InvocationCertificate program index (binaryArguments left right output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (operation (inputValue memory left) (inputValue memory right)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

theorem binary_checked (operation : BitVec 256 → BitVec 256 → BitVec 256) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (binaryBody profile callee))
    (child : InitializedBinaryResult operation program callee) :
    BinaryContract operation program index := by
  intro memory left right call
  obtain ⟨output, entered, entry, childCall, before, fresh⟩ := setup
    (binaryBody profile callee) (binaryArgs left right) rfl rfl rfl rfl program memory [left, right] call
  obtain ⟨childFuel, childResult, childCert, readback, _, outside⟩ :=
    child entered left right output childCall
  let bits := operation (inputValue entered left) (inputValue entered right)
  let bytes := numberBytes bits.toNat 32
  have hl := childCall.input_formed (reference := left) (by simp)
  have hr := childCall.input_formed (reference := right) (by simp)
  have ho := childCall.output_formed (reference := output) (by simp)
  have stepped : step (binaryBody profile callee) (.call callee 3) 3 (binaryArgs left right)
      (frame memory output) (binaryArguments left right output).reverse entered =
      .ok (.call callee (binaryArguments left right output) [] entered) := by
    simp [step, binaryArguments, checkedValue, formValue, hl, hr, ho, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run program 2 index 4 (binaryArgs left right) (frame memory output) [] childResult =
      .ok (leaveFrame (frame memory output) childResult, [.scalar (.aggregate bytes)]) := by
    apply Eq.trans
    · apply run_next (target := 5) (values := [.scalar (.aggregate bytes)])
        (nextFrame := frame memory output) (updated := childResult) found (by rfl)
      exact step_load_aggregate (size := 32) (reference := output) (by rfl) readback
    · apply run_return found (by rfl)
      · rfl
      · rfl
  obtain ⟨fuel, finish⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, childCert.1⟩ ⟨2, tail⟩
  have executed := (binary_prefix profile callee program index fuel found memory entered left right output childCall).trans finish
  have checked : (binaryArgs left right).mapM (checkedValue memory) = .ok (binaryArgs left right) := by
    simp [binaryArgs, checkedValue, formValue, call.input_formed (by simp : left ∈ [left, right]),
      call.input_formed (by simp : right ∈ [left, right]), checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked entry
  refine ⟨fuel + 3, _, bytes, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked entry live executed,
    by simp [bytes, numberBytes], ?_, ?_⟩
  · simp only [bytes, byteNumber_numberBytes, bits,
      show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
      BitVec.ofNat_toNat, BitVec.setWidth_eq,
      call.input_value_after_setup entry (by simp : left ∈ [left, right]),
      call.input_value_after_setup entry (by simp : right ∈ [left, right])]
  · intro id bound offset
    have after := leaveFrame_preserves_memory_below (frame memory output) childResult memory.nextIdentity
      (by intro owned member; simp only [frame, List.mem_singleton] at member; rw [member, fresh]; exact Nat.le_refl _)
    have growth := (enterFrame_fresh _ _ _ _ _ entry).1.next
    exact (after.cells id bound offset).trans ((outside id (Nat.lt_of_lt_of_le bound growth) offset
      (Or.inl (by rw [fresh]; exact Nat.ne_of_lt bound))).trans (before.cells id bound offset))

#print axioms binary_checked
#print axioms binary_prefix
end UInt256Model.Safety.AggregateReturn

namespace UInt256Model.Safety.AggregateReturn
open CIL.Safety UInt256Model.Safety

def unaryBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32],
    code := [.arg 0, .localAddr 0, .call callee 2, .local 0, .ret] }

def unaryArgs (input : Reference) : List Value :=
  [.reference (.address input)]

def UnaryContract (operation : BitVec 256 → BitVec 256)
    (program : CIL.Program) (index : Nat) : Prop :=
  ∀ memory input, CallingConditions program memory [input] [] →
    ∃ fuel final bytes,
      InvocationCertificate program index (unaryArgs input) memory fuel final [.scalar (.aggregate bytes)] ∧
      bytes.length = 32 ∧
      BitVec.ofNat 256 (CIL.Safety.byteNumber bytes) = operation (inputValue memory input) ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

theorem unary_prefix (profile : CIL.FeatureProfile) (callee : Nat)
    (program : CIL.Program) (index fuel : Nat)
    (found : program[index]? = some (unaryBody profile callee))
    (original entered : Memory) (input output : Reference)
    (call : CallingConditions program entered [input] [output]) :
    run program (fuel + 2) index 0 (unaryArgs input) (frame original output) [] entered =
      run program fuel index 2 (unaryArgs input) (frame original output)
        (unaryArguments input output).reverse entered := by
  have hl := call.input_formed (reference := input) (by simp)
  have ho := call.output_formed (reference := output) (by simp)
  iterate 2
    apply Eq.trans
    · apply run_next found
      · simp only [unaryBody]; rfl
      · simp (config := { implicitDefEqProofs := false }) only [step, unaryArgs, frame, List.getElem?_cons_zero,
          checkedValue, formValue, localAddress, hl, ho, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        rfl
  rfl

def InitializedUnaryResult (operation : BitVec 256 → BitVec 256)
    (program : CIL.Program) (index : Nat) : Prop :=
  ∀ memory input output, CallingConditions program memory [input] [output] →
    ∃ fuel final, InvocationCertificate program index (unaryArguments input output) memory fuel final [] ∧
      read final output 32 1 = .ok (numberBytes (operation (inputValue memory input)).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset

theorem unary_checked (operation : BitVec 256 → BitVec 256) (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (unaryBody profile callee))
    (child : InitializedUnaryResult operation program callee) :
    UnaryContract operation program index := by
  intro memory input call
  obtain ⟨output, entered, entry, childCall, before, fresh⟩ := setup
    (unaryBody profile callee) (unaryArgs input) rfl rfl rfl rfl program memory [input] call
  obtain ⟨childFuel, childResult, childCert, readback, _, outside⟩ :=
    child entered input output childCall
  let bits := operation (inputValue entered input)
  let bytes := numberBytes bits.toNat 32
  have hl := childCall.input_formed (reference := input) (by simp)
  have ho := childCall.output_formed (reference := output) (by simp)
  have stepped : step (unaryBody profile callee) (.call callee 2) 2 (unaryArgs input)
      (frame memory output) (unaryArguments input output).reverse entered =
      .ok (.call callee (unaryArguments input output) [] entered) := by
    simp [step, unaryArguments, checkedValue, formValue, hl, ho, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run program 2 index 3 (unaryArgs input) (frame memory output) [] childResult =
      .ok (leaveFrame (frame memory output) childResult, [.scalar (.aggregate bytes)]) := by
    apply Eq.trans
    · apply run_next (target := 4) (values := [.scalar (.aggregate bytes)])
        (nextFrame := frame memory output) (updated := childResult) found (by rfl)
      exact step_load_aggregate (size := 32) (reference := output) (by rfl) readback
    · apply run_return found (by rfl)
      · rfl
      · rfl
  obtain ⟨fuel, finish⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, childCert.1⟩ ⟨2, tail⟩
  have executed := (unary_prefix profile callee program index fuel found memory entered input output childCall).trans finish
  have checked : (unaryArgs input).mapM (checkedValue memory) = .ok (unaryArgs input) := by
    simp [unaryArgs, checkedValue, formValue, call.input_formed (by simp : input ∈ [input]),
      checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked entry
  refine ⟨fuel + 2, _, bytes, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked entry live executed,
    by simp [bytes, numberBytes], ?_, ?_⟩
  · simp only [bytes, byteNumber_numberBytes, bits,
      show (256 : Nat)^32 = 2^256 from rfl, Nat.mod_eq_of_lt (BitVec.isLt _),
      BitVec.ofNat_toNat, BitVec.setWidth_eq,
      call.input_value_after_setup entry (by simp : input ∈ [input])]
  · intro id bound offset
    have after := leaveFrame_preserves_memory_below (frame memory output) childResult memory.nextIdentity
      (by intro owned member; simp only [frame, List.mem_singleton] at member; rw [member, fresh]; exact Nat.le_refl _)
    have growth := (enterFrame_fresh _ _ _ _ _ entry).1.next
    exact (after.cells id bound offset).trans ((outside id (Nat.lt_of_lt_of_le bound growth) offset
      (Or.inl (by rw [fresh]; exact Nat.ne_of_lt bound))).trans (before.cells id bound offset))

#print axioms unary_checked
#print axioms unary_prefix
end UInt256Model.Safety.AggregateReturn
