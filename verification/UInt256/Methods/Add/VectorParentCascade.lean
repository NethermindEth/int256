import UInt256.Methods.Add.VectorParentBranch
import UInt256.Methods.Add.VectorParentRepairCall

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model

theorem vector_parent_repair_return (memory : Memory) (frame : Frame) (args : List Value) (flag : BitVec 32) :
    run Extracted.program 2 prepareParentIndex (parentRepairCall+1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, []) := by
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have fetched : prepareParentBody.code[parentRepairCall+1]? = some .pop := by rfl
  apply Eq.trans
  · apply run_next found fetched
    simp [step, pureArity, scalars, CIL.step, checkedValue, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact vector_parent_return memory frame args

theorem vector_parent_cascade (original entered current : Memory)
    (left right output sum mask incoming propagation : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame prepareParentBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity prepareParentSpecs frame.locals)
    (state : ReturnedState Extracted.program current [])
    (sumSlot : frame.locals[0]? = some (.bytes .vector256 sum))
    (maskSlot : frame.locals[1]? = some (.bytes .vector256 mask))
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagation))
    (a b : Limbs)
    (prepared : PrepareResult current output sum mask incoming propagation (value a) (value b)) :
    ∃ fuel final,
      run Extracted.program fuel prepareParentIndex (prepareCall+9)
        (binaryArguments left right output) frame [] current = .ok (final, []) ∧
      read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  have currentCall : CallingConditions Extracted.program current [] [output] := by
    refine ⟨⟨state.1, ?_, ?_⟩, state.2.2⟩
    · simp
    · intro view member
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
      subst view
      exact prepared.outputWritable
  obtain ⟨allocation, ready⟩ := access_requirements prepared.propagationWritable
  have advanced : original.nextIdentity ≤ current.nextIdentity := Nat.le_trans
    (homes.home_bound 3 _ _ propagationSlot) (Nat.le_of_lt (state.1.1 _ _ ready.present).1)
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [] ∧ read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex (prepareCall+9)
        (binaryArguments left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
    apply vector_parent_repair_call current output sum mask propagation frame
      (binaryArguments left right output) a b currentCall rfl sumSlot maskSlot propagationSlot
      prepared.sumRead prepared.maskRead prepared.propagationRead post
    intro after flag _ _ result writable footprint
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (reference := output) (by simp))
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    refine ⟨2, leaveFrame frame after, [], vector_parent_repair_return after frame _ flag,
      rfl, (teardown.read output old 32 1).trans result,
      (teardown.access output old 32 1 true).trans writable, ?_⟩
    intro id offset old notOutput
    exact (teardown.cells id old offset).trans
      (footprint id offset (Nat.lt_of_lt_of_le old advanced) notOutput)
  obtain ⟨fuel, final, returned, executed, same, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_parent_repair_return
#print axioms vector_parent_cascade
end UInt256Proof.Add.Safety
