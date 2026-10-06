import UInt256.Methods.Subtract.VectorSafetyBorrow
import UInt256.Methods.AddSubtract.VectorOutput
import UInt256.Arithmetic.SIMDBorrow
import UInt256.Arithmetic.PackedMasks
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Equality.Lemmas

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The first output write may overlap either input. Saved private values remain
    readable, and only the caller's output bytes change. -/
theorem vector_early_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (differenceHome incomingHome : Reference) (difference incoming : BitVec 256)
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (differenceRead : read current differenceHome 32 1 = .ok (numberBytes difference.toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) difference incoming).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have formed := currentCall.output_formed outputMember
  conv in vectorOutputStart => cbv
  iterate 2
    apply run_next_exists post found (by rfl)
    · simp [step, outputArgument, checkedValue, formValue, formed, checkedAt,
        instruction, staticInstruction, memoryInstruction, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact vector_output_checked original entered current inputs outputs output frame args
    call currentCall outputMember authority outputArgument (vectorOutputStart + 2) 2 4
    (.vector (.add64 256)) (CIL.Vector.zip256 (· + ·) difference incoming) (by rfl)
    differenceHome incomingHome difference incoming differenceSlot incomingSlot differenceRead incomingRead
    (by simp [CIL.Vector.intrinsic_add256]) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    post continuation

#print axioms vector_early_output_checked
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vectorTestStart : Nat := (vectorBody.code.findIdx fun op =>
  match op with | .intrinsic (.avx .testZ64) 2 => true | _ => false) - 2

def vectorFastReturn : Nat := match vectorBody.code[vectorTestStart + 3]? with
  | some (.brnonzero target) => target
  | _ => 0

/-- Branch on the actual saved propagation mask without reading caller inputs. -/
theorem vector_propagation_test (memory : Memory) (frame : Frame) (args : List Value)
    (equalHome incomingHome : Reference) (equal incoming : BitVec 256)
    (equalSlot : frame.locals[5]? = some (.bytes .vector256 equalHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (equalRead : read memory equalHome 32 1 = .ok (numberBytes equal.toNat 32))
    (incomingRead : read memory incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vectorIndex
        (if equal &&& incoming = 0 then vectorFastReturn else vectorTestStart + 4)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorTestStart args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have loadEqual := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 equal) equal.toNat rfl equalSlot equalRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 incoming) incoming.toNat rfl incomingSlot incomingRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  have testPC : vectorTestStart = vectorTestStart := rfl
  conv at testPC => rhs; cbv
  have returnPC : vectorFastReturn = vectorFastReturn := rfl
  conv at returnPC => rhs; cbv
  simp only [testPC, returnPC] at continuation
  rw [testPC]
  by_cases zero : equal &&& incoming = BitVec.ofNat 256 0
  all_goals
    simp only [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, zero, ite_true, ite_false] at continuation
    repeat' first
      | (simpa [zero] using continuation)
      | (simp (config := { failIfUnchanged := false }) [zero]
         apply run_next_exists post found (by rfl)
         first
         | exact loadEqual _ _
         | exact loadIncoming _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_testz256, zero, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_propagation_test

def equalLanes (a b : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) a b

/-- Generate the equality mask from saved operands, then take the checked
    propagation branch. No caller input load occurs after the output write. -/
theorem vector_propagation_checked (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftHome rightHome incomingHome : Reference) (a b incoming : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ equalHome after,
      frame.locals[5]? = some (.bytes .vector256 equalHome) →
      read after equalHome 32 1 = .ok (numberBytes (equalLanes a b).toNat 32) →
      MemoryBelow original.nextIdentity current after →
      MemoryBelow equalHome.allocation current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex
          (if equalLanes a b &&& incoming = 0 then vectorFastReturn else vectorTestStart + 4)
          args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  apply vector_binary_checked original entered current inputs outputs frame args currentCall
    enteredWF homes authority leftHome rightHome a b leftSlot rightSlot leftRead rightRead
    (vectorOutputStart + 8) 5 (by decide) (.vector (.eq64 256)) (equalLanes a b)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) post
  intro equalHome after equalSlot equalRead _ _ preserved afterCall afterAuthority earlier advanced
  have order := homes.ordered 4 5 .vector256 .vector256 incomingHome equalHome
    (by decide) incomingSlot equalSlot
  have retainedIncoming := (earlier.read incomingHome order 32 1).trans incomingRead
  exact vector_propagation_test after frame args equalHome incomingHome (equalLanes a b) incoming
    equalSlot incomingSlot equalRead retainedIncoming post
    (continuation equalHome after equalSlot equalRead preserved earlier afterCall afterAuthority advanced)

#print axioms vector_propagation_checked
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vectorFastFlag (mask : BitVec 256) : BitVec 32 :=
  if CIL.Vector.moveMask64 mask &&& 8 > 0 then 1 else 0

/-- The fast return reads the saved borrow mask, returns its high-lane flag,
    and expires only the current frame's owned allocations. -/
theorem vector_fast_return (memory : Memory) (frame : Frame) (args : List Value)
    (maskHome : Reference) (mask : BitVec 256)
    (slot : frame.locals[3]? = some (.bytes .vector256 maskHome))
    (loaded : read memory maskHome 32 1 = .ok (numberBytes mask.toNat 32)) :
    run Extracted.program 8 vectorIndex vectorFastReturn args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (vectorFastFlag mask))]) := by
  have loadMask := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 mask) mask.toNat rfl slot loaded
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  have returns : vectorBody.returnsValue = true := by rfl
  conv in vectorFastReturn => cbv
  iterate 7
    apply Eq.trans
    · apply run_next found (by rfl)
      first
      | exact loadMask _ _
      | (simp (config := { implicitDefEqProofs := false })
          [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.binary,
            CIL.Intrinsic.available, CIL.Vector.intrinsic_reinterpret256,
            CIL.Vector.intrinsic_movemask256, checkedValue, numericValue,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : vectorBody.code[vectorFastReturn + 7]? = some .ret := by rfl
  conv at fetched in vectorFastReturn => cbv
  simp [run, found, fetched, returns, step, vectorFastFlag, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_fast_return

theorem vector_fast_flag_masks : ∀ b0 b1 b2 b3 : Bool,
    vectorFastFlag (CIL.Vector.pack256 (CIL.Vector.mask64 b0) (CIL.Vector.mask64 b1)
      (CIL.Vector.mask64 b2) (CIL.Vector.mask64 b3)) = if b3 then 1 else 0 := by decide

theorem vector_fast_flag_top (a b : UInt256Model.Limbs) :
    vectorFastFlag (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)) =
      if a 3 < b 3 then 1 else 0 := by
  simp only [generatedBorrow, UInt256Proof.Equality.value_pack, CIL.Vector.zip256,
    CIL.Vector.lane256_0, CIL.Vector.lane256_1, CIL.Vector.lane256_2, CIL.Vector.lane256_3,
    vector_fast_flag_masks, BitVec.ult_eq_decide_lt, decide_eq_true_eq]

/-- Under the independent no-propagation condition, the returned high-lane bit
    is precisely unsigned 256-bit underflow. -/
theorem vector_fast_flag_underflow (a b : UInt256Model.Limbs)
    (noPropagation : UInt256Proof.NoBorrowPropagation a b) :
    vectorFastFlag (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)) =
      if (UInt256Model.value a).toNat < (UInt256Model.value b).toNat then 1 else 0 := by
  rw [vector_fast_flag_top]
  have chain := (UInt256Proof.independent_borrow_chain a b noPropagation).2.2
  have flag : (a 3 < b 3) ↔ (UInt256Model.value a).toNat < (UInt256Model.value b).toNat := by
    rw [← UInt256Proof.Reporting.finalBorrow_underflow]
    change _ ↔ UInt256Proof.finalBorrow a b ≠ 0
    change UInt256Proof.finalBorrow a b = UInt256Proof.independentBorrow (a 3) (b 3) at chain
    rw [chain, UInt256Proof.independentBorrow, UInt256Proof.borrow_initial]
    split <;> simp_all
  simp only [flag]

#print axioms vector_fast_flag_masks
#print axioms vector_fast_flag_top
#print axioms vector_fast_flag_underflow

theorem vector_propagation_mask (a b : UInt256Model.Limbs) :
    equalLanes (UInt256Model.value a) (UInt256Model.value b) &&&
      incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)) =
      UInt256Proof.propagation256 a b := by
  simp only [equalLanes, generatedBorrow, UInt256Proof.Equality.value_pack,
    CIL.Vector.zip256, CIL.Vector.lane256_0, CIL.Vector.lane256_1,
    CIL.Vector.lane256_2, CIL.Vector.lane256_3, incomingBorrow_packed,
    CIL.Vector.pack256_and, BitVec.ult_eq_decide_lt,
    UInt256Proof.propagation256, UInt256Proof.borrowMask]
  congr 1
  change _ &&& BitVec.ofNat 64 0 = BitVec.ofNat 64 0
  exact BitVec.and_zero

theorem vector_fast_branch_underflow (a b : UInt256Model.Limbs)
    (fast : equalLanes (UInt256Model.value a) (UInt256Model.value b) &&&
      incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)) = 0) :
    vectorFastFlag (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)) =
      if (UInt256Model.value a).toNat < (UInt256Model.value b).toNat then 1 else 0 := by
  rw [vector_propagation_mask] at fast
  exact vector_fast_flag_underflow a b (UInt256Proof.propagation256_zero a b fast)

#print axioms vector_propagation_mask
#print axioms vector_fast_branch_underflow

/-- The vector result written before the propagation test is the independent
    four-limb speculative subtraction, expressed without interpreter state. -/
theorem vector_speculative_value (a b : UInt256Model.Limbs) :
    CIL.Vector.zip256 (· + ·)
      (CIL.Vector.zip256 (· - ·) (UInt256Model.value a) (UInt256Model.value b))
      (incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b))) =
      UInt256Model.value (UInt256Proof.speculativeDifference a b) := by
  simp only [generatedBorrow, UInt256Proof.Equality.value_pack, CIL.Vector.zip256,
    CIL.Vector.lane256_0, CIL.Vector.lane256_1, CIL.Vector.lane256_2, CIL.Vector.lane256_3,
    incomingBorrow_packed, BitVec.ult_eq_decide_lt, UInt256Proof.borrow_mask_subtract_raw]
  simp [UInt256Proof.speculativeDifference, show (3 : Fin 4).val = 3 from rfl]

/-- The actual fast-branch condition makes the stored vector exactly the
    initial unsigned operands' difference modulo 2^256. -/
theorem vector_fast_difference (a b : UInt256Model.Limbs)
    (fast : equalLanes (UInt256Model.value a) (UInt256Model.value b) &&&
      incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b)) = 0) :
    CIL.Vector.zip256 (· + ·)
      (CIL.Vector.zip256 (· - ·) (UInt256Model.value a) (UInt256Model.value b))
      (incomingBorrow (generatedBorrow (UInt256Model.value a) (UInt256Model.value b))) =
      UInt256Model.value a - UInt256Model.value b := by
  rw [vector_speculative_value]
  rw [vector_propagation_mask] at fast
  exact UInt256Proof.speculative_difference_value a b (UInt256Proof.propagation256_zero a b fast)

#print axioms vector_speculative_value
#print axioms vector_fast_difference
end UInt256Proof.Subtract.Safety
