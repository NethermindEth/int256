import UInt256.Methods.Add.ScalarMemory
import UInt256.Methods.Add.SmallChecked
import UInt256.Methods.Add.SafetyResult

namespace UInt256Proof.Safety

open CIL.Safety

def scalarSmallDecision (swapped : Bool) : Nat :=
  if swapped then scalarSecondDecision else scalarFirstDecision

def scalarSmallCall (swapped : Bool) : Nat :=
  let first := Extracted.addScalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.addScalarUInt64Index
    | _ => false
  if swapped then first + 1 + (Extracted.addScalarBody.code.drop (first + 1)).findIdx (fun op =>
    match op with | .call callee _ => callee == Extracted.addScalarUInt64Index | _ => false)
  else first

def scalarSmallSource (swapped : Bool) (left right : Reference) : Reference :=
  if swapped then right else left

theorem scalar_small_prefix (swapped : Bool) (left right output home : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory) {flag : BitVec 32}
    (formed : form memory (scalarSmallSource swapped left right) = .ok (scalarSmallSource swapped left right))
    (outputFormed : form memory output = .ok output)
    (slot : frame.locals[if swapped then 1 else 0]? = some (.bytes .word64 home))
    (loaded : read memory home 8 1 = .ok (numberBytes word.toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarSmallCall swapped)
        (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame
        [.reference (.address output), .scalar (.i64 word),
          .reference (.address (scalarSmallSource swapped left right))] memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarSmallDecision swapped)
        (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame [.scalar (.i64 0)] memory = .ok (result, returned) ∧
      post result returned := by
  have reading := load_local_word64_of_read loaded
  cases swapped
  all_goals
    conv in (scalarSmallDecision _) => cbv
    conv at continuation in (scalarSmallCall _) => cbv
    dsimp [scalarSmallSource] at formed continuation
    dsimp at slot
    repeat'
      first
      | exact continuation
      | simp (config := { failIfUnchanged := false })
        apply run_next_exists post
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, scalarArguments, UInt256Model.Safety.binaryArguments, step,
              checkedValue, numericValue, formValue, formed, outputFormed, slot, reading,
              pureArity, scalars, CIL.step, CIL.truth, checkedAt, Except.mapError,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_small_return (swapped : Bool) (args : List Value) (flag : BitVec 32)
    (frame : Frame) (memory : Memory) :
    run Extracted.program 1 Extracted.addScalarIndex (scalarSmallCall swapped + 1)
      args frame [.scalar (.i32 flag)] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  cases swapped
  all_goals
    conv in (scalarSmallCall _) => cbv
    simp only [Nat.reduceAdd]
    rw [run]
    simp [cil_code, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_small_prefix
#print axioms scalar_small_return

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem scalar_small_finish (swapped : Bool) (original entered current : CIL.Safety.Memory)
    (frame : Frame) (left right output : Reference) (word : BitVec 64) {flag : BitVec 32}
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) original =
      .ok (frame, entered))
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (sum : inputValue current (scalarSmallSource swapped left right) + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right)
    (naturalSum : (inputValue current (scalarSmallSource swapped left right)).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarIndex (scalarSmallCall swapped)
        (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame
        [.reference (.address output), .scalar (.i64 word),
          .reference (.address (scalarSmallSource swapped left right))] current = .ok (final, values) ∧
      AddResult original final values left right output := by
  have member : scalarSmallSource swapped left right ∈ [left, right] := by
    cases swapped <;> simp [scalarSmallSource]
  have selected : CallingConditions Extracted.program current [scalarSmallSource swapped left right] [output] := by
    refine ⟨⟨currentCall.1.1, ?_, currentCall.1.2.2⟩, currentCall.2⟩
    intro view included
    have same : view = wordView (scalarSmallSource swapped left right) := by simpa using included
    subst view
    exact currentCall.1.2.1 _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  have inputFormed := currentCall.input_formed member
  have outputFormed := currentCall.output_formed (by simp : output ∈ [output])
  obtain ⟨childFuel, after, values, invoked, result⟩ :=
    small_checked current (scalarSmallSource swapped left right) output word selected
  rw [result.flagValue] at invoked
  have methodFound : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by
    simp only [cil_code]
  have instructionFound : Extracted.addScalarBody.code[scalarSmallCall swapped]? =
      some (.call Extracted.addScalarUInt64Index 3) := by
    cases swapped
    all_goals conv in (scalarSmallCall _) => cbv
    all_goals simp only [cil_code]
  have stepped : step Extracted.addScalarBody (.call Extracted.addScalarUInt64Index 3)
      (scalarSmallCall swapped) (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame
      [.reference (.address output), .scalar (.i64 word),
        .reference (.address (scalarSmallSource swapped left right))] current =
        .ok (.call Extracted.addScalarUInt64Index
          (smallArguments (scalarSmallSource swapped left right) output word) [] current) := by
    simp [step, smallArguments, checkedValue, numericValue, formValue, inputFormed, outputFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned := scalar_small_return swapped (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)])
    (smallOverflow current (scalarSmallSource swapped left right) word) frame after
  obtain ⟨fuel, finished⟩ := run_call_exists methodFound instructionFound stepped
    ⟨childFuel, invoked⟩ ⟨1, returned⟩
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retained := leaveFrame_preserves_memory_below frame after original.nextIdentity
    (fun id included => (fresh.2 id included).1)
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  have bytes : (fun offset => ((leaveFrame frame after).cells output.allocation offset).bits) =
      (fun offset => (after.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨fuel, leaveFrame frame after,
    [.scalar (.i32 (smallOverflow current (scalarSmallSource swapped left right) word))], finished,
    ⟨leaveFrame_preserves_wellFormed _ _ result.wellFormed, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [inputValue, bytes] using result.value.trans sum
  · simp only [smallOverflow, naturalSum, addOverflow]
  · exact (retained.access output outputOld 32 1 true).trans result.writable
  · intro id old offset outside
    exact (retained.cells id old offset).trans
      ((result.footprint id (Nat.lt_of_lt_of_le old next) offset outside).trans (preserved.cells id old offset))

#print axioms scalar_small_finish

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem input_small_value (memory : CIL.Safety.Memory) (reference : Reference)
    (small : inputLimb memory reference 1 ||| inputLimb memory reference 2 |||
      inputLimb memory reference 3 = 0) :
    inputValue memory reference = BitVec.ofNat 256 (inputLimb memory reference 0).toNat := by
  obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp small
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
  have initial : UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
    UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset
  rw [← initial, ← UInt256Proof.singleLimb_eq (inputLimb memory reference) h1 h2 h3]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

theorem scalar_small_values (swapped : Bool) (original current : CIL.Safety.Memory)
    (left right output : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (small : inputLimb original (if swapped then left else right) 1 |||
      inputLimb original (if swapped then left else right) 2 |||
      inputLimb original (if swapped then left else right) 3 = 0) :
    let word := inputLimb original (if swapped then left else right) 0
    (inputValue current (scalarSmallSource swapped left right) + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right) ∧
    ((inputValue current (scalarSmallSource swapped left right)).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) := by
  have smallValue := input_small_value original (if swapped then left else right) small
  have wideBound : (inputLimb original (if swapped then left else right) 0).toNat < 2^256 :=
    Nat.lt_trans (inputLimb original (if swapped then left else right) 0).isLt (by decide)
  have preservedValue : ∀ reference ∈ [left, right], inputValue current reference = inputValue original reference := by
    intro reference member
    simp only [inputValue, call.input_bytes_of_memory_below preserved member]
  cases swapped
  · have kept := preservedValue left (by simp)
    dsimp at smallValue wideBound ⊢
    simp [scalarSmallSource, kept, smallValue, Nat.mod_eq_of_lt wideBound]
  · have kept := preservedValue right (by simp)
    dsimp at smallValue wideBound ⊢
    simp [scalarSmallSource, kept, smallValue, Nat.mod_eq_of_lt wideBound, BitVec.add_comm, Nat.add_comm]

theorem scalar_private_next (original entered current : CIL.Safety.Memory) (frame : Frame)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (enteredWF : entered.WellFormed) (currentWF : current.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) : original.nextIdentity ≤ current.nextIdentity := by
  have specified : scalarLocalSpecs[0]? = some (some 0) := by simp [scalarLocalSpecs, cil_code]
  obtain ⟨reference, _, fresh, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have currentWrite := authority.access writable (enteredWF.1 _ _ ready.present).1
  obtain ⟨currentAllocation, currentReady⟩ := access_requirements currentWrite
  exact Nat.le_trans fresh (Nat.le_of_lt (currentWF.1 _ _ currentReady.present).1)

#print axioms input_small_value
#print axioms scalar_small_values
#print axioms scalar_private_next

end UInt256Proof.Safety
