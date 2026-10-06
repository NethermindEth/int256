import UInt256.Methods.AddSubtract.VectorStore

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The actual preparation helper stores independent lane sums through its
    sum output argument, retaining both private input snapshots. -/
theorem vector_sum_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[3]? = some (.reference (.address output)))
    (leftHome rightHome : Reference) (a b : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) a b).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOperandStart + 13) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOperandStart + 8) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have formed := currentCall.output_formed outputMember
  apply run_next_exists (target := vectorOperandStart + 9)
    (values := [.reference (.address output)]) (nextFrame := frame) (updated := current)
    post found (by rfl)
  · simp [step, outputArgument, checkedValue, formValue, formed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · exact vector_store_checked original entered current inputs outputs output frame args
      call currentCall outputMember authority (vectorOperandStart + 9) 0 1
      (.vector (.add64 256)) (CIL.Vector.zip256 (· + ·) a b) (by rfl)
      leftHome rightHome a b leftSlot rightSlot leftRead rightRead
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) post continuation

#print axioms vector_sum_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Snapshot both inputs before the preparation helper writes its lane sums.
    Subsequent carry detection retains the initial operands even with overlap. -/
theorem vector_sum_prefix_checked (original entered : Memory)
    (inputs outputs : List Reference) (left right sum : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (sumMember : sum ∈ outputs)
    (leftArgument : args[0]? = some (.reference (.address left)))
    (rightArgument : args[1]? = some (.reference (.address right)))
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ leftHome rightHome after,
      frame.locals[0]? = some (.bytes .vector256 leftHome) →
      frame.locals[1]? = some (.bytes .vector256 rightHome) →
      read after leftHome 32 1 = .ok (numberBytes (inputValue original left).toNat 32) →
      read after rightHome 32 1 = .ok (numberBytes (inputValue original right).toNat 32) →
      read after sum 32 1 = .ok (numberBytes
        (CIL.Vector.zip256 (· + ·) (inputValue original left) (inputValue original right)).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      (∀ id offset, id < original.nextIdentity → OutsideOutput sum id offset →
        after.cells id offset = original.cells id offset) →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOperandStart + 13) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector_operand_dispatch entered frame args post
  apply vector_operands_checked original entered inputs outputs left right frame args call setup homes
    leftMember rightMember leftArgument rightArgument post
  intro leftHome rightHome current leftSlot rightSlot _ leftRead rightRead preserved currentCall authority firstNext
  apply vector_sum_checked original entered current inputs outputs sum frame args call currentCall
    sumMember authority sumArgument leftHome rightHome (inputValue original left) (inputValue original right)
    leftSlot rightSlot leftRead rightRead post
  intro after sumRead afterCall afterAuthority outside privateReads next
  apply continuation leftHome rightHome after leftSlot rightSlot
    (privateReads _ _ _ _ (homes.home_bound 0 _ _ leftSlot) leftRead)
    (privateReads _ _ _ _ (homes.home_bound 1 _ _ rightSlot) rightRead)
    sumRead afterCall afterAuthority (Nat.le_trans firstNext next)
  intro id offset old notSum
  exact (outside id offset notSum).trans (preserved.cells id old offset)

#print axioms vector_sum_prefix_checked
end UInt256Proof.Add.Safety
