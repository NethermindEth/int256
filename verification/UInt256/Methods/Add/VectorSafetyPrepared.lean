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
