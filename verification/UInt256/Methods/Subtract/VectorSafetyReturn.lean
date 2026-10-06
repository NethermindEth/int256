import UInt256.Methods.Subtract.VectorSafetyPropagation
import UInt256.Arithmetic.SIMDBorrow
import UInt256.Arithmetic.PackedMasks
import UInt256.Methods.Reporting.Arithmetic
import UInt256.Methods.Equality.Lemmas

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
