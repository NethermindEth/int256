import UInt256.Methods.Add.VectorCarryFlags
import UInt256.Methods.Add.VectorParentCall
import UInt256.Methods.Add.VectorParentRepairCall

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def reportingFastReturn : Nat := match prepareParentBody.code[prepareCall + 4]? with
  | some (.brnonzero target) => target
  | _ => 0

/-- Read only the initialized private masks, then follow the extracted branch.
    Neither outcome rereads potentially overwritten caller inputs. -/
theorem vector_reporting_branch (memory : Memory) (frame : Frame) (args : List Value)
    (propagationHome incomingHome : Reference) (propagation incoming : BitVec 256)
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagationHome))
    (incomingSlot : frame.locals[2]? = some (.bytes .vector256 incomingHome))
    (propagationRead : read memory propagationHome 32 1 = .ok (numberBytes propagation.toNat 32))
    (incomingRead : read memory incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex
        (if propagation &&& incoming = BitVec.ofNat 256 0 then reportingFastReturn else prepareCall + 5)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex (prepareCall + 1) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have loadPropagation := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 propagation) propagation.toNat rfl propagationSlot propagationRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 incoming) incoming.toNat rfl incomingSlot incomingRead
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have profile : prepareParentBody.profile = Extracted.profile := by rfl
  have callPC : prepareCall = prepareCall := rfl
  conv at callPC => rhs; cbv
  have returnPC : reportingFastReturn = reportingFastReturn := rfl
  conv at returnPC => rhs; cbv
  simp only [callPC, returnPC] at continuation
  rw [callPC]
  by_cases zero : propagation &&& incoming = BitVec.ofNat 256 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    repeat' first
      | (simpa [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, zero] using continuation)
      | (simp (config := { failIfUnchanged := false }) [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, zero]
         apply run_next_exists post found (by rfl)
         first
         | exact loadPropagation _ _
         | exact loadIncoming _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.binary,
               CIL.Intrinsic.available, CIL.Vector.intrinsic_and256,
               CIL.Vector.intrinsic_reinterpret256, CIL.Vector.intrinsic_movemask256, CIL.Vector.intrinsic_testz256,
               show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, zero, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

theorem vector_reporting_fast_return (memory : Memory) (frame : Frame) (args : List Value)
    (maskHome : Reference) (mask : BitVec 256)
    (slot : frame.locals[1]? = some (.bytes .vector256 maskHome))
    (loaded : read memory maskHome 32 1 = .ok (numberBytes mask.toNat 32)) :
    run Extracted.program 8 prepareParentIndex reportingFastReturn args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32
        (if CIL.Vector.moveMask64 mask &&& BitVec.ofNat 32 8 > BitVec.ofNat 32 0 then 1 else 0))]) := by
  have loadMask := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 mask) mask.toNat rfl slot loaded
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have profile : prepareParentBody.profile = Extracted.profile := by rfl
  have returns : prepareParentBody.returnsValue = true := by rfl
  conv in reportingFastReturn => cbv
  iterate 7
    apply Eq.trans
    · apply run_next found (by rfl)
      first
      | exact loadMask _ _
      | (simp (config := { implicitDefEqProofs := false })
          [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.binary,
            CIL.Intrinsic.available, CIL.Vector.intrinsic_reinterpret256, CIL.Vector.intrinsic_movemask256,
            checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : prepareParentBody.code[27]? = some .ret := by rfl
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_reporting_branch
#print axioms vector_reporting_fast_return
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model

theorem vector_reporting_repair_return (memory : Memory) (frame : Frame) (args : List Value) (flag : BitVec 32) :
    run Extracted.program 1 prepareParentIndex (parentRepairCall+1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have fetched : prepareParentBody.code[parentRepairCall+1]? = some .ret := by rfl
  have returns : prepareParentBody.returnsValue = true := by rfl
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem vector_reporting_cascade (original entered current : Memory)
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
      run Extracted.program fuel prepareParentIndex (prepareCall+5)
        (binaryArguments left right output) frame [] current = .ok (final, [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))]) ∧
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
    returned = [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))] ∧ read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset
  have finish : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex (prepareCall+5)
        (binaryArguments left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
    apply vector_parent_repair_call current output sum mask propagation frame
      (binaryArguments left right output) a b currentCall rfl sumSlot maskSlot propagationSlot
      prepared.sumRead prepared.maskRead prepared.propagationRead post
    intro after flag flagValue _ result writable footprint
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (reference := output) (by simp))
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    refine ⟨1, leaveFrame frame after, _, vector_reporting_repair_return after frame _ flag,
      by rw [flagValue], (teardown.read output old 32 1).trans result,
      (teardown.access output old 32 1 true).trans writable, ?_⟩
    intro id offset old notOutput
    exact (teardown.cells id old offset).trans
      (footprint id offset (Nat.lt_of_lt_of_le old advanced) notOutput)
  obtain ⟨fuel, final, returned, executed, same, result, writable, footprint⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_reporting_repair_return
#print axioms vector_reporting_cascade
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model

/-- The parent's fast suffix returns the mathematical sum and retires only its
    private frame. Caller output remains initialized and writable. -/
theorem vector_reporting_fast (original entered current : Memory)
    (left right output sum mask incoming propagation : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame prepareParentBody (binaryArguments left right output) original =
      .ok (frame, entered))
    (maskSlot : frame.locals[1]? = some (.bytes .vector256 mask))
    (incomingSlot : frame.locals[2]? = some (.bytes .vector256 incoming))
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagation))
    (a b : Limbs)
    (prepared : PrepareResult current output sum mask incoming propagation (value a) (value b))
    (fast : (propagationMask (CIL.Vector.zip256 (· + ·) (value a) (value b))) &&&
      (incomingCarry (generatedCarry (value a) (value b))) = BitVec.ofNat 256 0) :
    ∃ fuel final,
      run Extracted.program fuel prepareParentIndex (prepareCall + 1)
        (binaryArguments left right output) frame [] current = .ok (final, [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      MemoryBelow original.nextIdentity current final := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))] ∧
    read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
    access final output 32 1 true = .ok () ∧
    MemoryBelow original.nextIdentity current final
  have finish : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex (prepareCall + 1)
        (binaryArguments left right output) frame [] current = .ok (final, returned) ∧
      post final returned := by
    apply vector_reporting_branch current frame (binaryArguments left right output)
      propagation incoming _ _ propagationSlot incomingSlot
      prepared.propagationRead prepared.incomingRead post
    simp only [fast, ite_true]
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have teardown := leaveFrame_preserves_memory_below frame current original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (reference := output) (by simp))
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    have returned := vector_reporting_fast_return current frame (binaryArguments left right output)
      mask (generatedCarry (value a) (value b)) maskSlot prepared.maskRead
    rw [vector_fast_overflow a b fast] at returned
    refine ⟨8, leaveFrame frame current, _, returned, rfl, ?_, ?_, teardown⟩
    · rw [teardown.read output old 32 1]
      have result := prepared.outputRead
      have shortGuard : parentPropagationBits
          (propagationMask (CIL.Vector.zip256 (· + ·) (value a) (value b)))
          (incomingCarry (generatedCarry (value a) (value b))) = BitVec.ofNat 32 0 := by
        rw [parentPropagationBits, fast]
        decide
      rw [vector_fast_sum a b shortGuard] at result
      exact result
    · exact (teardown.access output old 32 1 true).trans prepared.outputWritable
  obtain ⟨fuel, final, returned, executed, same, result, writable, retained⟩ := finish
  subst returned
  exact ⟨fuel, final, executed, result, writable, retained⟩

#print axioms vector_reporting_fast
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model

theorem vector_reporting_branches (original entered current : Memory)
    (left right output sum mask incoming propagation : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame prepareParentBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity prepareParentSpecs frame.locals)
    (state : ReturnedState Extracted.program current [])
    (sumSlot : frame.locals[0]? = some (.bytes .vector256 sum))
    (maskSlot : frame.locals[1]? = some (.bytes .vector256 mask))
    (incomingSlot : frame.locals[2]? = some (.bytes .vector256 incoming))
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagation))
    (a b : Limbs)
    (prepared : PrepareResult current output sum mask incoming propagation (value a) (value b)) :
    ∃ fuel final,
      run Extracted.program fuel prepareParentIndex (prepareCall+1)
        (binaryArguments left right output) frame [] current = .ok (final, [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))]) ∧
      read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  by_cases fast : (propagationMask (CIL.Vector.zip256 (· + ·) (value a) (value b))) &&&
      (incomingCarry (generatedCarry (value a) (value b))) = BitVec.ofNat 256 0
  · obtain ⟨fuel, final, executed, result, writable, preserved⟩ := vector_reporting_fast
      original entered current left right output sum mask incoming propagation frame call setup
      maskSlot incomingSlot propagationSlot a b prepared fast
    exact ⟨fuel, final, executed, result, writable, fun id offset old _ => preserved.cells id old offset⟩
  · let post : Memory → List Value → Prop := fun final returned =>
      returned = [.scalar (.i32 (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0))] ∧ read final output 32 1 = .ok (numberBytes (value a + value b).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset
    have finish : ∃ fuel final returned,
        run Extracted.program fuel prepareParentIndex (prepareCall+1)
          (binaryArguments left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
      apply vector_reporting_branch current frame (binaryArguments left right output) propagation incoming _ _
        propagationSlot incomingSlot prepared.propagationRead prepared.incomingRead post
      simp only [fast, ite_false]
      obtain ⟨fuel, final, executed, result, writable, footprint⟩ := vector_reporting_cascade
        original entered current left right output sum mask incoming propagation frame call setup homes state
        sumSlot maskSlot propagationSlot a b prepared
      exact ⟨fuel, final, _, executed, rfl, result, writable, footprint⟩
    obtain ⟨fuel, final, returned, executed, same, result, writable, footprint⟩ := finish
    subst returned
    exact ⟨fuel, final, executed, result, writable, footprint⟩

#print axioms vector_reporting_branches
end UInt256Proof.Add.Safety
