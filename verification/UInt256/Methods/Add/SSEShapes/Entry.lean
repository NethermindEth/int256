import UInt256.Methods.Add.SSEShapes.Repair
import UInt256.Methods.Add.ARMFlag

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- `seg` sits at instruction `base` of `code`. -/
def At (code : List CIL.Op) (base : Nat) (seg : List CIL.Op) : Prop :=
  ∃ leading tail : List CIL.Op, leading.length = base ∧ code = leading ++ seg ++ tail

/-- Any concrete placement is witnessed by `take`/`drop`. -/
theorem at_of_eq {code seg : List CIL.Op} {base : Nat} (bound : base ≤ code.length)
    (placed : code = code.take base ++ seg ++ code.drop (base + seg.length)) : At code base seg :=
  ⟨code.take base, code.drop (base + seg.length), by simp [bound], placed⟩

/-- Positions of the SSE vector helper's segments after the shared 37-instruction start. -/
structure Layout where
  incomingDoubled : Bool
  incoming : Nat
  earlyDoubled : Bool
  propagation : Nat
  decisionDoubled : Bool
  combine : Nat
  merge : Option Nat
  join : Nat
  fast : Nat
  repairDoubled : Bool
  repair : Nat

/-- The helper body follows `layout`: guards, incoming, correction, early output, propagation, decision, fast suffix. -/
structure Shaped (body : CIL.Method) (layout : Layout) : Prop where
  incomingGuard : At body.code 37 (guardCode layout.incomingDoubled layout.incoming)
  incoming : At body.code layout.incoming sseIncomingCode
  correction : At body.code (layout.incoming + 12) correctionCode
  early : At body.code (layout.incoming + 19) (earlyCode layout.earlyDoubled layout.propagation)
  propagation : At body.code layout.propagation propagationCode
  decisionGuard : At body.code (layout.propagation + 12) (guardCode layout.decisionDoubled layout.combine)
  combine : At body.code layout.combine (combineCode layout.merge layout.join)
  join : At body.code layout.join (joinCode layout.fast)
  repairGuard : At body.code (layout.join + 5) (guardCode layout.repairDoubled layout.repair)
  fast : At body.code layout.fast (sseFastCode layout.fast)

/-- Execution from entry through the four input loads, both lane sums and both carry masks. -/
def StartContract (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec) : Prop :=
  ∀ (original entered : Memory) (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value),
    CallingConditions program original inputs outputs →
    enterFrame body args original = .ok (frame, entered) →
    frame.locals = .root (some .null) :: slots →
    NumericHomes entered original.nextIdentity specs slots →
    left ∈ inputs → right ∈ inputs →
    args[0]? = some (.reference (.address left)) →
    args[1]? = some (.reference (.address right)) →
    ∀ (post : Memory → List Value → Prop),
    (∀ sum lowMask highMask after,
      slots[4]? = some (.bytes .vector128 sum) →
      slots[5]? = some (.bytes .vector128 lowMask) →
      slots[6]? = some (.bytes .vector128 highMask) →
      read after sum 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 4).toNat 16) →
      read after lowMask 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 5).toNat 16) →
      read after highMask 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 6).toNat 16) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 37 args (vector128SavedFrame frame slots right)
          [.scalar (.v128 (halfSum (inputHalf original left 0) (inputHalf original right 0)))] after =
            .ok (result, returned) ∧ post result returned) →
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered = .ok (result, returned) ∧ post result returned

/-- The extracted 37-instruction start satisfies the start contract. -/
theorem prefix_start (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128AddPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec) :
    StartContract program body method specs := by
  intro original entered inputs outputs left right frame slots args call setup layout homes leftMember rightMember
    leftArg rightArg post continuation
  apply vector128_start_checked program body method specs found tail code firstSeven original entered inputs outputs
    left right frame slots args call setup layout homes leftMember rightMember leftArg rightArg post
  intro _ sum lowMask highMask after _ sumSlot lowSlot highSlot sumRead lowRead highRead _ preserved afterCall
    afterAuthority advanced
  exact continuation sum lowMask highMask after sumSlot lowSlot highSlot sumRead lowRead highRead preserved afterCall
    afterAuthority advanced

/-- Repair path from its entry: exact sum, overflow flag, writable output and caller bytes kept. -/
def RepairContract (program : CIL.Program) (method : Nat) (specs : List NumericLocalSpec)
    (repair : Nat) : Prop :=
  ∀ (original entered current : Memory) (frame : Frame) (slots : List LocalSlot)
    (left right output : Reference) (args : List Value),
    frame.locals = .root (some (.address right)) :: slots →
    CallingConditions program original [left, right] [output] →
    CallingConditions program current [left, right] [output] →
    MemoryBelow original.nextIdentity original current →
    NumericHomes entered original.nextIdentity specs slots →
    entered.WellFormed →
    AccessBelow entered.nextIdentity entered current →
    args[0]? = some (.reference (.address left)) →
    args[1]? = some (.reference (.address right)) →
    args[2]? = some (.reference (.address output)) →
    (∀ id ∈ frame.owned, original.nextIdentity ≤ id) →
    ∃ fuel final values,
      run program fuel method repair args frame [] current = .ok (final, values) ∧
      AddResult original final values left right output

/-- The extracted carry-call repair at `repair` satisfies the repair contract. -/
theorem call_repair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (repair carry storage : Nat) (reversed : Bool)
    (placed : At body.code repair (repairCodeOf reversed carry storage))
    (carryFound : program[carry]? = some (carryBody body.profile))
    (storageFound : program[storage]? = some (repairStorage reversed body.profile))
    (wordSpecs : ∀ i : Fin 5, specs[14 + i.val]? = some armWordSpec)
    (returns : body.returnsValue = true) :
    RepairContract program method specs repair := by
  intro original entered current frame slots left right output args layout call currentCall preserved homes
    enteredWF authority leftArg rightArg outputArg owned
  obtain ⟨leading, tail, leadingLength, code⟩ := placed
  apply sse_repair_carry program body method specs found leading tail repair leadingLength carry storage reversed code carryFound
    wordSpecs original entered current frame (.root (some (.address right))) slots layout left right output
    call currentCall preserved homes enteredWF authority args leftArg rightArg
  intro carryHome results after state
  exact sse_finish program body method found leading tail repair leadingLength carry storage reversed code storageFound returns
    original after frame left right output carryHome results args outputArg call owned state

#print axioms at_of_eq
#print axioms prefix_start
#print axioms call_repair
end UInt256Proof.Add.SSEShapes
