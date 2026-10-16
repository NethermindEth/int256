import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.ConstructorSafety
import CIL.Safety.ConstructComposition

namespace UInt256Proof.Multiply.Entry
open CIL.Safety UInt256Model.Safety

def encoded (value : BitVec 256) : CIL.Value := .aggregate (numberBytes value.toNat 32)
def conversionBody (profile : CIL.FeatureProfile) (narrow : Bool) (constructor : Nat) : CIL.Method :=
  { profile := profile, locals := [], returnsValue := true,
    code := [.arg 0] ++ (if narrow then [.convU8] else []) ++
      [.const32 0, .convI8, .const32 0, .convI8, .const32 0, .convI8, .newAggregate constructor 4 32, .ret] }
def primitiveBody (profile : CIL.FeatureProfile) (firstScalar : Bool) (multiply conversion : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.aggregate (List.replicate 32 0), .aggregate (List.replicate 32 0)],
    localKinds := [.aggregate 32, .aggregate 32],
    code := [.arg (if firstScalar then 0 else 1), .call conversion 1, .setLocal 0,
      (if firstScalar then .localAddr 0 else .arg 0), (if firstScalar then .arg 1 else .localAddr 0),
      .localAddr 1, .call multiply 3, .local 1, .ret] }
structure PrimitiveContext extends Context where
  wrapperIndex : Nat
  conversionIndex : Nat
  constructorIndex : Nat
  narrow : Bool
  firstScalar : Bool
  wrapper : program[wrapperIndex]? = some (primitiveBody profile firstScalar indices.entry conversionIndex)
  conversion : program[conversionIndex]? = some (conversionBody profile narrow constructorIndex)
  constructor : program[constructorIndex]? = some (UInt256Proof.ConstructorSafety.body profile)
end UInt256Proof.Multiply.Entry
namespace UInt256Proof.Multiply.Entry
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety
def conversionWords (word : BitVec 64) : List Value :=
  [.scalar (.i64 word), .scalar (.i64 0), .scalar (.i64 0), .scalar (.i64 0)]

def ConversionPrefix (ctx : PrimitiveContext) (argument : CIL.Value) (word : BitVec 64) : Prop :=
  ∀ (memory : Memory) (frame : Frame) (post : Memory → List Value → Prop),
    (∃ fuel final values,
      run ctx.program fuel ctx.conversionIndex (if ctx.narrow then 8 else 7) [.scalar argument] frame
        (conversionWords word).reverse memory = .ok (final, values) ∧ post final values) →
    ∃ fuel final values,
      run ctx.program fuel ctx.conversionIndex 0 [.scalar argument] frame [] memory =
        .ok (final, values) ∧ post final values

theorem conversion_invoke (ctx : PrimitiveContext) (memory : Memory) (argument : CIL.Value) (word : BitVec 64)
    (numeric : numericValue argument = true) (prefixProof : ConversionPrefix ctx argument word)
    (call : CallingConditions ctx.program memory [] []) :
    ∃ fuel final,
      invoke ctx.program fuel ctx.conversionIndex [.scalar argument] memory =
        .ok (final, [.scalar (encoded (BitVec.ofNat 256 word.toNat))]) ∧
      final.WellFormed ∧ AccessBelow memory.nextIdentity memory final ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  let args := [Value.scalar argument]
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have found : ctx.program[ctx.conversionIndex]? = some (conversionBody ctx.profile ctx.narrow ctx.constructorIndex) := ctx.conversion
  have checked : (conversionWords word).mapM (checkedValue memory) = .ok (conversionWords word) := by
    simp [conversionWords, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨temporary, updated, stepped, updatedCall, _, preserved, fresh⟩ :=
    call.new_aggregate256 (pc := (if ctx.narrow then 8 else 7)) (callee := ctx.constructorIndex) args (conversionWords word) [] frame memory found checked
  let nextFrame := { frame with owned := temporary.allocation :: frame.owned }
  obtain ⟨constructed, invoked, valid, outside, authority, _, loaded⟩ :=
    constructor_contract ctx.profile ctx.program ctx.constructorIndex ctx.constructor updated [] temporary word 0 0 0 updatedCall
  have childInvoke : invoke ctx.program 13 ctx.constructorIndex
      (.reference (.address temporary) :: conversionWords word) updated = .ok (constructed, []) := invoked
  have childLoad : loadLocal constructed (.bytes (.aggregate 32) temporary) =
      .ok (.scalar (encoded (BitVec.ofNat 256 word.toNat))) := by simpa [encoded, packed, UInt256Model.value] using loaded
  have returned : run ctx.program 1 ctx.conversionIndex ((if ctx.narrow then 8 else 7) + 1) args nextFrame
      [.scalar (encoded (BitVec.ofNat 256 word.toNat))] constructed =
      .ok (leaveFrame nextFrame constructed, [.scalar (encoded (BitVec.ofNat 256 word.toNat))]) := by
    have fetched : (conversionBody ctx.profile ctx.narrow ctx.constructorIndex).code[(if ctx.narrow then 8 else 7) + 1]? = some .ret := by cases h : ctx.narrow <;> simp [conversionBody]
    have returns : (conversionBody ctx.profile ctx.narrow ctx.constructorIndex).returnsValue = true := by cases h : ctx.narrow <;> simp [conversionBody]
    simp [run, found, fetched, returns, step, checkedValue, numericValue, encoded, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_construct_exists found (by cases h : ctx.narrow <;> simp [conversionBody, conversionWords]) stepped ⟨13, childInvoke⟩ childLoad ⟨1, returned⟩
  have body : ∃ fuel final returned,
      run ctx.program fuel ctx.conversionIndex 0 args frame [] memory = .ok (final, returned) ∧
      final = leaveFrame nextFrame constructed ∧ returned = [.scalar (encoded (BitVec.ofNat 256 word.toNat))] := by
    apply prefixProof memory frame
      (fun final returned => final = leaveFrame nextFrame constructed ∧
        returned = [.scalar (encoded (BitVec.ofNat 256 word.toNat))])
    exact ⟨tailFuel, _, _, tail, rfl, rfl⟩
  obtain ⟨fuel, final, returnedValues, ran, rfl, rfl⟩ := body
  have checkedArgs : args.mapM (checkedValue memory) = .ok args := by
    simp [args, checkedValue, numeric, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (conversionBody ctx.profile ctx.narrow ctx.constructorIndex) args memory = .ok (frame, memory) := by
    have kinds : (conversionBody ctx.profile ctx.narrow ctx.constructorIndex).localKinds = [] := by cases h : ctx.narrow <;> simp [conversionBody]
    have locals : (conversionBody ctx.profile ctx.narrow ctx.constructorIndex).locals = [] := by cases h : ctx.narrow <;> simp [conversionBody]
    have aggregates : (conversionBody ctx.profile ctx.narrow ctx.constructorIndex).parameterHomes = [] := by cases h : ctx.narrow <;> simp [conversionBody]
    simp [enterFrame, conversionBody, makeLocals, makeParameterHomes, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : invoke ctx.program fuel ctx.conversionIndex args memory =
      .ok (leaveFrame nextFrame constructed, [.scalar (encoded (BitVec.ofNat 256 word.toNat))]) := by
    exact invoke_of_run found checkedArgs setup ran
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
end UInt256Proof.Multiply.Entry
