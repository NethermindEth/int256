import UInt256.Methods.AddSubtract.Vector128References

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Save all four initial input halves before arithmetic or caller output writes.
    Fresh numeric homes, rather than caller disjointness, preserve earlier reads. -/
theorem vector128_inputs_checked (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vector128Body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ l0 l1 r0 r1 after,
      slots[0]? = some (.bytes .vector128 l0) →
      slots[1]? = some (.bytes .vector128 l1) →
      slots[2]? = some (.bytes .vector128 r0) →
      slots[3]? = some (.bytes .vector128 r1) →
      read after l0 16 1 = .ok (numberBytes (inputHalf original left 0).toNat 16) →
      read after l1 16 1 = .ok (numberBytes (inputHalf original left 1).toNat 16) →
      read after r0 16 1 = .ok (numberBytes (inputHalf original right 0).toNat 16) →
      read after r1 16 1 = .ok (numberBytes (inputHalf original right 1).toNat 16) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 22 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have authority : AccessBelow entered.nextIdentity entered entered := (MemoryBelow.refl _ _).accessBelow
  let saved := vector128SavedFrame frame slots right
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have savedRoot : saved.locals[0]? = some (.root (some (.address right))) := rfl
  apply vector128_reference_prefix entered left right frame slots (some .null) layout args leftArg rightArg
    (enteredCall.input_formed leftMember) (enteredCall.input_formed rightMember) post
  apply vector128_operand_checked original entered entered inputs outputs left saved
    (.root (some (.address right))) slots args [.reference (.address left)] savedLayout
    call enteredCall leftMember enteredCall.1.1 homes preserved authority false false post
  intro l0 m0 s0 read0 p0 c0 a0 w0
  apply vector128_left_upper m0 inputs outputs left saved args c0 leftMember post
  apply vector128_operand_checked original entered m0 inputs outputs left saved
    (.root (some (.address right))) slots args [] savedLayout
    call c0 leftMember enteredCall.1.1 homes p0 a0 false true post
  intro l1 m1 s1 read1 p1 c1 a1 w1
  apply vector128_right_reference m1 inputs outputs right saved args savedRoot c1 rightMember false post
  apply vector128_operand_checked original entered m1 inputs outputs right saved
    (.root (some (.address right))) slots args [] savedLayout
    call c1 rightMember enteredCall.1.1 homes p1 a1 true false post
  intro r0 m2 s2 read2 p2 c2 a2 w2
  apply vector128_right_reference m2 inputs outputs right saved args savedRoot c2 rightMember true post
  apply vector128_operand_checked original entered m2 inputs outputs right saved
    (.root (some (.address right))) slots args [] savedLayout
    call c2 rightMember enteredCall.1.1 homes p2 a2 true true post
  intro r1 after s3 read3 p3 c3 a3 w3
  simp only [vector128OperandLocal, Bool.false_eq_true, ite_false, ite_true,
    Nat.reduceAdd, savedLayout, List.getElem?_cons_succ] at s0 s1 s2 s3
  have o01 := homes.ordered 0 1 .vector128 .vector128 l0 l1 (by decide) s0 s1
  have o02 := homes.ordered 0 2 .vector128 .vector128 l0 r0 (by decide) s0 s2
  have o03 := homes.ordered 0 3 .vector128 .vector128 l0 r1 (by decide) s0 s3
  have o12 := homes.ordered 1 2 .vector128 .vector128 l1 r0 (by decide) s1 s2
  have o13 := homes.ordered 1 3 .vector128 .vector128 l1 r1 (by decide) s1 s3
  have o23 := homes.ordered 2 3 .vector128 .vector128 r0 r1 (by decide) s2 s3
  have kept0 := write_preserves_disjoint_read w3
    (write_preserves_disjoint_read w2
      (write_preserves_disjoint_read w1 read0 (Or.inl (Nat.ne_of_lt o01)))
      (Or.inl (Nat.ne_of_lt o02))) (Or.inl (Nat.ne_of_lt o03))
  have kept1 := write_preserves_disjoint_read w3
    (write_preserves_disjoint_read w2 read1 (Or.inl (Nat.ne_of_lt o12))) (Or.inl (Nat.ne_of_lt o13))
  have kept2 := write_preserves_disjoint_read w3 read2 (Or.inl (Nat.ne_of_lt o23))
  exact continuation l0 l1 r0 r1 after s0 s1 s2 s3 kept0 kept1 kept2 read3 p3 c3 a3
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (Nat.le_trans (write_extends_allocations _ _ _ _ _ w2).next
          (write_extends_allocations _ _ _ _ _ w3).next)))

#print axioms vector128_inputs_checked
end UInt256Proof.AddSubtract.Safety
