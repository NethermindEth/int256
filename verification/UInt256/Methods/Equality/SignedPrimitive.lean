import UInt256.Safety.StepEquation
import UInt256.Methods.Equality.UnsignedPrimitive

namespace UInt256Proof.Equality.SignedPrimitive
open CIL.Safety UInt256Model.Safety
/-- A proved invocation of the actual called method, including memory safety.
    This obligation is discharged by the selected scalar or vector child proof. -/
def SignedChild (program : CIL.Program) (signedCallee : Nat) (argument : CIL.Value) (bits : BitVec 256) : Prop :=
  ∀ memory left, CallingConditions program memory [left] [] →
    ∃ fuel final,
      InvocationCertificate program signedCallee (scalarArguments left argument) memory fuel final
        [.scalar (.i32 (if inputValue memory left = bits then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset

def SignedNegative (program : CIL.Program) (signedIndex : Nat) (argument : CIL.Value) : Prop :=
  ∀ memory left frame, CallingConditions program memory [left] [] →
    ∃ fuel, run program fuel signedIndex 0
      (scalarArguments left argument) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 0)])

def SignedPositive (program : CIL.Program) (signedIndex signedCall : Nat) (argument : CIL.Value) : Prop :=
  ∀ memory left frame, CallingConditions program memory [left] [] →
    ∀ post : Memory → List Value → Prop,
      (∃ fuel final values,
        run program fuel signedIndex signedCall
          (scalarArguments left argument) frame
          [.scalar argument, .reference (.address left)] memory = .ok (final, values) ∧
        post final values) →
      ∃ fuel final values,
        run program fuel signedIndex 0 (scalarArguments left argument) frame [] memory =
          .ok (final, values) ∧ post final values

variable (program : CIL.Program) (signedIndex signedCall signedCallee : Nat) (signedBody : CIL.Method)
  (lookup : program[signedIndex]? = some signedBody)
  (fetched : signedBody.code[signedCall]? = some (.call signedCallee 2))
  (retFetched : signedBody.code[signedCall + 1]? = some (.ret (some .unsigned8)))
  (returns : signedBody.returnsValue = true)
  (locals : signedBody.locals = []) (kinds : signedBody.localKinds = [])
  (vectors : signedBody.vectorArgs = []) (homes : signedBody.parameterHomes = [])

include lookup retFetched returns in
 theorem signed_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : Memory)
    (boolean : flag = 0 ∨ flag = 1) :
    run program 1 signedIndex (signedCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  rcases boolean with rfl | rfl <;>
    simp [run, lookup, retFetched, step, returns, checkedValue, numericValue, CIL.NarrowKind.extend,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

include lookup fetched retFetched returns locals kinds vectors homes in
theorem signed_checked (memory : Memory) (left : Reference) (argument : CIL.Value) (bits : BitVec 256)
    (negative : Bool) (numeric : numericValue argument = true)
    (child : SignedChild program signedCallee argument bits)
    (negativeExecution : negative = true → SignedNegative program signedIndex argument)
    (positiveExecution : negative = false → SignedPositive program signedIndex signedCall argument)
    (call : CallingConditions program memory [left] []) :
    ∃ fuel final,
      InvocationCertificate program signedIndex (scalarArguments left argument)
        memory fuel final [.scalar (.i32
          (if negative then 0 else if inputValue memory left = bits then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have setup : enterFrame signedBody (scalarArguments left argument) memory = .ok (frame, memory) := by
    simp [enterFrame, locals, kinds, vectors, homes, makeLocals, makeArgumentHomes, makeParameterHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have formed := call.input_formed (reference := left) (by simp)
  have checked : (scalarArguments left argument).mapM (checkedValue memory) =
      .ok (scalarArguments left argument) := by
    simp [scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  cases sign : negative
  · simp only [Bool.false_eq_true, ite_false]
    obtain ⟨childFuel, childFinal, certificate, cells⟩ :=
      child memory left call
    have stepped : step signedBody (.call signedCallee 2) signedCall
        (scalarArguments left argument) frame [.scalar argument, .reference (.address left)] memory =
        .ok (.call signedCallee (scalarArguments left argument) [] memory) := by
      simp [step, scalarArguments, checkedValue, formValue, numeric, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨tailFuel, tail⟩ := run_call_exists lookup fetched stepped
      ⟨childFuel, certificate.1⟩ ⟨1, signed_return program signedIndex signedCall signedBody lookup retFetched returns _ _ frame childFinal (by split <;> simp)⟩
    let post : Memory → List Value → Prop := fun result values =>
      result = leaveFrame frame childFinal ∧ values = [.scalar (.i32
        (if inputValue memory left = bits then 1 else 0))]
    obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
      positiveExecution sign memory left frame call post ⟨tailFuel, _, _, tail, rfl, rfl⟩
    subst final
    subst values
    refine ⟨fuel, leaveFrame frame childFinal, ?_, ?_⟩
    · exact certify_invocation program signedIndex signedBody
        (scalarArguments left argument) memory frame memory fuel _ _ lookup checked setup live finished
    · simpa only [leaveFrame, frame, List.foldl_nil] using cells
  · simp only [ite_true]
    obtain ⟨fuel, finished⟩ := negativeExecution sign memory left frame call
    refine ⟨fuel, leaveFrame frame memory, ?_, ?_⟩
    · exact certify_invocation program signedIndex signedBody
        (scalarArguments left argument) memory frame memory fuel _ _ lookup checked setup live finished
    · simp [leaveFrame, frame]

#print axioms signed_checked



def body32 (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 1,
  .const32 0,
  .blt 7,
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8),
  .const32 0,
  .ret (some .unsigned8)] }

def body64 (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 1,
  .const32 0,
  .convI8,
  .blt 8,
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8),
  .const32 0,
  .ret (some .unsigned8)] }

macro "negative_steps" found:term "," negative:term : tactic => `(tactic|
  (intro memory left frame call
   refine ⟨16, ?_⟩
   simp [run, $found:term, body32, body64, step, scalarArguments, checkedValue, numericValue,
     pureArity, scalars, instruction, CIL.step.eq_def, CIL.unary, CIL.NarrowKind.extend, $negative:term,
     Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]))

macro "positive_steps" found:term "," nonnegative:term : tactic => `(tactic|
  (intro memory left frame call post continuation
   have formed := call.input_formed (reference := left) (by simp)
   repeat' first
     | exact continuation
     | (apply run_next_exists post $found
        · simp only [body32, body64]; rfl
        · simp [body32, body64, step, scalarArguments, checkedValue, numericValue, formValue, formed,
            pureArity, scalars, instruction, CIL.step.eq_def, CIL.unary, $nonnegative:term,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩))))

theorem negative32 (profile : CIL.FeatureProfile) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body32 profile callee)) (right : BitVec 32) (negative : right.toInt < 0) :
    SignedNegative program entry (.i32 right) := by
  negative_steps found, negative

theorem positive32 (profile : CIL.FeatureProfile) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body32 profile callee)) (right : BitVec 32) (positive : ¬right.toInt < 0) :
    SignedPositive program entry 5 (.i32 right) := by
  positive_steps found, positive

theorem negative64 (profile : CIL.FeatureProfile) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body64 profile callee)) (right : BitVec 64) (negative : right.toInt < 0) :
    SignedNegative program entry (.i64 right) := by
  negative_steps found, negative

theorem positive64 (profile : CIL.FeatureProfile) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body64 profile callee)) (right : BitVec 64) (positive : ¬right.toInt < 0) :
    SignedPositive program entry 6 (.i64 right) := by
  positive_steps found, positive

#print axioms negative32
#print axioms positive32
#print axioms negative64
#print axioms positive64


theorem checked32 (profile : CIL.FeatureProfile) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body32 profile callee))
    (child : ScalarOperatorContract false false CIL.Value.i32
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program callee) :
    ScalarOperatorContract false false CIL.Value.i32
      (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) program entry := by
  intro memory left word call
  have child' : SignedChild program callee (.i32 word) (BitVec.ofNat 256 word.toNat) := by
    intro memory left call
    simpa only [scalarOperatorArguments, Bool.false_eq_true, ite_false, Bool.bne_false, decide_eq_true_eq]
      using child memory left word call
  have result := signed_checked program entry 5 callee (body32 profile callee)
    found rfl rfl rfl rfl rfl rfl rfl memory left (.i32 word) (BitVec.ofNat 256 word.toNat)
    (decide (word.toInt < 0)) rfl child'
    (fun negative => negative32 profile program entry callee found word (by simpa using negative))
    (fun positive => positive32 profile program entry callee found word (by simpa using positive)) call
  by_cases sign : word.toInt < 0 <;>
    simpa [scalarOperatorArguments, sign] using result

#print axioms checked32
theorem checked64 (profile : CIL.FeatureProfile) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (body64 profile callee))
    (child : ScalarOperatorContract false false CIL.Value.i64
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program callee) :
    ScalarOperatorContract false false CIL.Value.i64
      (fun input word => !decide (word.toInt < 0) && decide (input = BitVec.ofNat 256 word.toNat)) program entry := by
  intro memory left word call
  have child' : SignedChild program callee (.i64 word) (BitVec.ofNat 256 word.toNat) := by
    intro memory left call
    simpa only [scalarOperatorArguments, Bool.false_eq_true, ite_false, Bool.bne_false, decide_eq_true_eq]
      using child memory left word call
  have result := signed_checked program entry 6 callee (body64 profile callee)
    found rfl rfl rfl rfl rfl rfl rfl memory left (.i64 word) (BitVec.ofNat 256 word.toNat)
    (decide (word.toInt < 0)) rfl child'
    (fun negative => negative64 profile program entry callee found word (by simpa using negative))
    (fun positive => positive64 profile program entry callee found word (by simpa using positive)) call
  by_cases sign : word.toInt < 0 <;>
    simpa [scalarOperatorArguments, sign] using result

#print axioms checked64
end UInt256Proof.Equality.SignedPrimitive
