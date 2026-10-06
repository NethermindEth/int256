import UInt256.Methods.ConstructorSafety
import UInt256.Safety.ConstructorSetup
import CIL.Safety.ConstructComposition
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

def conversionIndex : Nat := Extracted.program.findIdx fun body =>
  body.locals.isEmpty && body.code.any (fun op => match op with | .newValue _ _ => true | _ => false)

def conversionBody : CIL.Method := Extracted.program[conversionIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def conversionWords (word : BitVec 64) : List Value :=
  [.scalar (.i64 word), .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0)]

def conversionCall : Nat := conversionBody.code.findIdx fun op =>
  match op with | .newValue _ _ => true | _ => false

def ConversionPrefix (argument : CIL.Value) (word : BitVec 64) : Prop :=
  ∀ (memory : Memory) (frame : Frame) (post : Memory → List Value → Prop),
    (∃ fuel final values,
      run Extracted.program fuel conversionIndex conversionCall [.scalar argument] frame
        (conversionWords word).reverse memory = .ok (final, values) ∧ post final values) →
    ∃ fuel final values,
      run Extracted.program fuel conversionIndex 0 [.scalar argument] frame [] memory =
        .ok (final, values) ∧ post final values

theorem conversion_invoke (memory : Memory) (argument : CIL.Value) (word : BitVec 64)
    (numeric : numericValue argument = true) (prefixProof : ConversionPrefix argument word)
    (call : CallingConditions Extracted.program memory [] []) :
    ∃ fuel final,
      invoke Extracted.program fuel conversionIndex [.scalar argument] memory =
        .ok (final, [.scalar (.v256 (BitVec.ofNat 256 word.toNat))]) ∧
      final.WellFormed ∧ AccessBelow memory.nextIdentity memory final ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  let args := [Value.scalar argument]
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : Extracted.program[conversionIndex]? = some conversionBody := by rfl
  have checked : (conversionWords word).mapM (checkedValue memory) = .ok (conversionWords word) := by
    simp [conversionWords, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨temporary, updated, stepped, updatedCall, _, preserved, fresh⟩ :=
    call.new_value (pc := conversionCall) (callee := constructorIndex) args (conversionWords word) [] frame memory found checked
  let nextFrame := { frame with owned := temporary.allocation :: frame.owned }
  obtain ⟨childFuel, constructed, invoked, valid, outside, authority, _, loaded⟩ :=
    constructor_contract updated [] temporary word 0 0 0 updatedCall
  have childInvoke : invoke Extracted.program childFuel constructorIndex
      (.reference (.address temporary) :: conversionWords word) updated = .ok (constructed, []) := invoked
  have childLoad : loadValue constructed (.address temporary) 32 =
      .ok (.v256 (BitVec.ofNat 256 word.toNat)) := by simpa using loaded
  have returned : run Extracted.program 1 conversionIndex (conversionCall + 1) args nextFrame
      [.scalar (.v256 (BitVec.ofNat 256 word.toNat))] constructed =
      .ok (leaveFrame nextFrame constructed, [.scalar (.v256 (BitVec.ofNat 256 word.toNat))]) := by
    have fetched : conversionBody.code[conversionCall + 1]? = some .ret := by rfl
    have returns : conversionBody.returnsValue = true := by rfl
    simp [run, found, fetched, returns, step, checkedValue, numericValue, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_construct_exists found (by rfl) stepped ⟨childFuel, childInvoke⟩ childLoad ⟨1, returned⟩
  have body : ∃ fuel final returned,
      run Extracted.program fuel conversionIndex 0 args frame [] memory = .ok (final, returned) ∧
      final = leaveFrame nextFrame constructed ∧ returned = [.scalar (.v256 (BitVec.ofNat 256 word.toNat))] := by
    apply prefixProof memory frame
      (fun final returned => final = leaveFrame nextFrame constructed ∧
        returned = [.scalar (.v256 (BitVec.ofNat 256 word.toNat))])
    exact ⟨tailFuel, _, _, tail, rfl, rfl⟩
  obtain ⟨fuel, final, returnedValues, ran, rfl, rfl⟩ := body
  have checkedArgs : args.mapM (checkedValue memory) = .ok args := by
    simp [args, checkedValue, numeric, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame conversionBody args memory = .ok (frame, memory) := by
    have kinds : conversionBody.localKinds = [] := by rfl
    have locals : conversionBody.locals = [] := by rfl
    have aggregates : conversionBody.aggregateArgs = [] := by rfl
    simp [enterFrame, kinds, locals, aggregates, makeLocals, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : invoke Extracted.program fuel conversionIndex args memory =
      .ok (leaveFrame nextFrame constructed, [.scalar (.v256 (BitVec.ofNat 256 word.toNat))]) := by
    simpa only [invoke, found, checkedArgs, setup, Except.mapError, Bind.bind, Except.bind] using ran
  have growth := step_extends_allocations _ _ _ _ _ _ _ _ stepped
  have retained := leaveFrame_preserves_memory_below nextFrame constructed memory.nextIdentity (by
    intro id member
    simp only [nextFrame, frame, List.mem_cons, List.not_mem_nil, or_false] at member
    subst id
    exact Nat.le_of_eq fresh.symm)
  refine ⟨fuel, _, finished, leaveFrame_preserves_wellFormed _ _ valid.1.1,
    (preserved.accessBelow.trans (authority.weaken growth.next)).trans retained.accessBelow, ?_⟩
  intro id old offset
  have distinct : id ≠ temporary.allocation := by rw [fresh]; exact Nat.ne_of_lt old
  exact (retained.cells id old offset).trans
    ((outside id offset (Or.inl distinct)).trans (preserved.cells id old offset))

#print axioms conversion_invoke
end UInt256Proof.Multiply.Safety
