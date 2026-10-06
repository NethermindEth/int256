import UInt256.Methods.Add.VectorSafetyIncoming

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The helper's output arguments are private homes supplied by its caller.
    Their separation is an internal call obligation, not an input/output alias
    restriction on public addition. -/
theorem vector_prepare_checked (original entered : Memory)
    (inputs outputs : List Reference) (left right sum mask incoming : Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (sumMember : sum ∈ outputs) (maskMember : mask ∈ outputs) (incomingMember : incoming ∈ outputs)
    (sumMask : sum.allocation ≠ mask.allocation)
    (sumIncoming : sum.allocation ≠ incoming.allocation)
    (maskIncoming : mask.allocation ≠ incoming.allocation)
    (leftArgument : args[0]? = some (.reference (.address left)))
    (rightArgument : args[1]? = some (.reference (.address right)))
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (maskArgument : args[4]? = some (.reference (.address mask)))
    (incomingArgument : args[5]? = some (.reference (.address incoming)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after sum 32 1 = .ok (numberBytes
        (CIL.Vector.zip256 (· + ·) (inputValue original left) (inputValue original right)).toNat 32) →
      read after mask 32 1 = .ok (numberBytes
        (generatedCarry (inputValue original left) (inputValue original right)).toNat 32) →
      read after incoming 32 1 = .ok (numberBytes
        (incomingCarry (generatedCarry (inputValue original left) (inputValue original right))).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      (∀ id offset, id < original.nextIdentity →
        OutsideOutput sum id offset → OutsideOutput mask id offset → OutsideOutput incoming id offset →
        after.cells id offset = original.cells id offset) →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex vectorOutputStart args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector_sum_prefix_checked original entered inputs outputs left right sum frame args call setup homes
    leftMember rightMember sumMember leftArgument rightArgument sumArgument post
  intro leftHome rightHome current leftSlot rightSlot leftRead rightRead sumRead currentCall authority advanced footprint
  apply vector_carry_dispatch current frame args post
  apply vector_carry_checked original entered current inputs outputs sum mask frame args call currentCall
    sumMember maskMember authority sumArgument maskArgument leftHome rightHome (inputValue original left) (inputValue original right)
    leftSlot rightSlot rightRead leftRead sumRead post
  intro middle maskWrite maskRead middleCall middleAuthority maskOutside _ maskNext
  have retainedSum := write_preserves_disjoint_read maskWrite sumRead (Or.inl sumMask)
  apply vector_incoming_checked original entered middle inputs outputs mask incoming frame args call middleCall
    maskMember incomingMember middleAuthority maskArgument incomingArgument
    (generatedCarry (inputValue original left) (inputValue original right)) maskRead post
  intro after incomingWrite incomingRead afterCall afterAuthority incomingOutside _ incomingNext
  apply continuation after
    (write_preserves_disjoint_read incomingWrite retainedSum (Or.inl sumIncoming))
    (write_preserves_disjoint_read incomingWrite maskRead (Or.inl maskIncoming))
    incomingRead afterCall afterAuthority (Nat.le_trans advanced (Nat.le_trans maskNext incomingNext))
  intro id offset old notSum notMask notIncoming
  exact (incomingOutside id offset notIncoming).trans
    ((maskOutside id offset notMask).trans (footprint id offset old notSum))

#print axioms vector_prepare_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Execute SkipInit and the first caller-output store from initialized private
    sum and incoming-carry snapshots, without rereading either original input. -/
theorem vector_early_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output sum incoming : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs) (sumMember : sum ∈ outputs) (incomingMember : incoming ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (incomingArgument : args[5]? = some (.reference (.address incoming)))
    (sumValue incomingValue : BitVec 256)
    (sumRead : read current sum 32 1 = .ok (numberBytes sumValue.toNat 32))
    (incomingRead : read current incoming 32 1 = .ok (numberBytes incomingValue.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current output (numberBytes (CIL.Vector.zip256 (· - ·) sumValue incomingValue).toNat 32) 1 = .ok after →
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· - ·) sumValue incomingValue).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOutputStart + 10) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs output
      (CIL.Vector.zip256 (· - ·) sumValue incomingValue) call currentCall outputMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  have outputFormed := currentCall.output_formed outputMember
  have sumFormed := currentCall.output_formed sumMember
  have incomingFormed := currentCall.output_formed incomingMember
  have loadSum := vector_load_snapshot current sum sumValue sumRead
  have loadIncoming := vector_load_snapshot current incoming incomingValue incomingRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at done in vectorOutputStart => cbv
  conv in vectorOutputStart => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, outputArgument, sumArgument, incomingArgument,
           outputFormed, sumFormed, incomingFormed, loadSum, loadIncoming,
           pureArity, scalars, CIL.step, CIL.Intrinsic.available, CIL.Vector.intrinsic_sub256,
           checkedValue, numericValue, formValue, instruction, staticInstruction, memoryInstruction,
           storeValue, referenceAt, written, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector_early_output_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def propagationMask (sum : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) sum (~~~(BitVec.ofNat 256 0))

/-- The propagation test reads the saved lane sums after the caller-output write.
    Its initialized snapshot must therefore be preserved by that write. -/
theorem vector_propagation_checked (original entered current : Memory)
    (inputs outputs : List Reference) (sum propagation : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (sumMember : sum ∈ outputs) (propagationMember : propagation ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (propagationArgument : args[6]? = some (.reference (.address propagation)))
    (sumValue : BitVec 256)
    (sumRead : read current sum 32 1 = .ok (numberBytes sumValue.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current propagation (numberBytes (propagationMask sumValue).toNat 32) 1 = .ok after →
      read after propagation 32 1 = .ok (numberBytes (propagationMask sumValue).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput propagation id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOutputStart + 16) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOutputStart + 10) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs propagation (propagationMask sumValue)
      call currentCall propagationMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  simp [propagationMask] at written
  have sumFormed := currentCall.output_formed sumMember
  have propagationFormed := currentCall.output_formed propagationMember
  have reading := vector_load_snapshot current sum sumValue sumRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at done in vectorOutputStart => cbv
  conv in vectorOutputStart => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, sumArgument, propagationArgument, sumFormed, propagationFormed, reading,
           pureArity, scalars, CIL.step, CIL.Intrinsic.available, propagationMask,
           CIL.Vector.intrinsic_ones256, CIL.Vector.intrinsic_eq256,
           checkedValue, numericValue, formValue, staticInstruction, memoryInstruction,
           storeValue, referenceAt, written, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem vector_prepare_return (memory : Memory) (frame : Frame) (args : List Value) :
    run Extracted.program 1 vectorIndex (vectorOutputStart + 16) args frame [] memory =
      .ok (leaveFrame frame memory, []) := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have fetched : vectorBody.code[vectorOutputStart + 16]? = some .ret := by rfl
  have returns : vectorBody.returnsValue = false := by rfl
  simp [run, found, fetched, returns, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_propagation_checked
#print axioms vector_prepare_return
end UInt256Proof.Add.Safety
