import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Safety.ParameterSetup32
import UInt256.Methods.Compare.PrimitiveLeafContract
import CIL.Safety.CallComposition
import CIL.Safety.GuardNormalization

namespace UInt256Proof.Compare.PrimitiveValue
open CIL.Safety UInt256Model.Safety

def arguments (word : BitVec 64) (value : BitVec 256) : List Value :=
  [.scalar (.i64 word), aggregate256 value]

def body (callee : Nat) : CIL.Method :=
  { profile := PrimitiveLeaf.scalarProfile, returnsValue := true, locals := [],
    parameterHomes := [(1, .aggregate 32)],
    code := [.localAddr 0, .arg 0, .call callee 2, .const32 0, .eq, .ret (some .unsigned8)] }

def Contract (program : CIL.Program) (index : Nat) : Prop :=
  ∀ memory (word : BitVec 64) (value : BitVec 256), CallingConditions program memory [] [] →
    ∃ fuel final,
      InvocationCertificate program index (arguments word value) memory fuel final
        [.scalar (.i32 (if word.toNat ≤ value.toNat then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

theorem value_prefix (program : CIL.Program) (index callee fuel : Nat)
    (found : program[index]? = some (body callee))
    (memory entered : Memory) (copy : Reference) (word : BitVec 64) (value : BitVec 256)
    (call : CallingConditions program entered [copy] []) :
    run program (fuel + 2) index 0 (arguments word value) (parameterFrame32 memory copy) [] entered =
      run program fuel index 2 (arguments word value) (parameterFrame32 memory copy)
        [.scalar (.i64 word), .reference (.address copy)] entered := by
  have formed := call.input_formed (reference := copy) (by simp)
  iterate 2
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false }) only [step, arguments, parameterFrame32,
          List.getElem?_cons_zero, checkedValue, numericValue, ↓reduceIte, formValue, localAddress,
          formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        rfl
  rfl

theorem returned (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (body callee)) (args : List Value)
    (frame : Frame) (memory : Memory) (less : Bool) :
    run program 3 index 3 args frame [.scalar (.i32 (if less then 1 else 0))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if less then 0 else 1))]) := by
  cases less <;> simp [run, found, body, step, cil_guard, observerCount, pureArity, scalars, CIL.step, CIL.binary,
    CIL.NarrowKind.extend, instruction, checkedValue, numericValue, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem correctness (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (body callee))
    (childFound : program[callee]? = some (PrimitiveLeaf.method false false)) :
    Contract program index := by
  intro memory word value call
  obtain ⟨copy, entered, setup, enteredCall, copyValue, before, fresh⟩ :=
    parameter_setup32 (body callee) (arguments word value) value rfl rfl rfl rfl rfl program memory [] call
  obtain ⟨childFuel, childFinal, certificate, cells⟩ :=
    PrimitiveLeaf.checked_template false false program callee childFound entered copy word enteredCall
  have positive (flag : Bool) : (flag != false) = flag := by cases flag <;> rfl
  simp only [positive, PrimitiveSafety.predicate, Bool.false_eq_true, ite_false, copyValue] at certificate
  have formed := enteredCall.input_formed (reference := copy) (by simp)
  have stepped : step (body callee) (.call callee 2) 2 (arguments word value)
      (parameterFrame32 memory copy) [.scalar (.i64 word), .reference (.address copy)] entered =
      .ok (.call callee (scalarOperatorArguments false copy (.i64 word)) [] entered) := by
    simp [step, cil_guard, observerCount, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have suffix := returned program index callee found (arguments word value) (parameterFrame32 memory copy)
    childFinal (decide ((value.toNat : Int) < (word.toNat : Int)))
  have arithmetic : (if decide ((value.toNat : Int) < (word.toNat : Int)) then (0 : BitVec 32) else 1) =
      (if word.toNat ≤ value.toNat then 1 else 0) := by
    by_cases ordered : word.toNat ≤ value.toNat
    · have opposite : ¬ (value.toNat : Int) < (word.toNat : Int) := by omega
      simp [ordered, opposite]
    · have opposite : (value.toNat : Int) < (word.toNat : Int) := by omega
      simp [ordered, opposite]
  rw [arithmetic] at suffix
  obtain ⟨fuel, finish⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, certificate.1⟩ ⟨3, suffix⟩
  have executed := (value_prefix program index callee fuel found memory entered copy word value enteredCall).trans finish
  have checked : (arguments word value).mapM (checkedValue memory) = .ok (arguments word value) := by
    rfl
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨fuel + 2, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live executed, ?_⟩
  have growth := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below (parameterFrame32 memory copy) childFinal memory.nextIdentity
    (fun id member => (growth.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((cells id (Nat.lt_of_lt_of_le bound growth.1.next) offset).trans (before.cells id bound offset))

#print axioms value_prefix
#print axioms returned
#print axioms correctness
end UInt256Proof.Compare.PrimitiveValue
