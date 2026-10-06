import UInt256.Methods.Subtract.VectorSafetyArithmetic
import CIL.SIMD.Evaluation256Lemmas
import UInt256.Arithmetic.SignMasks

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def incomingBorrow (mask : BitVec 256) : BitVec 256 :=
  CIL.Vector.permute4x64 mask 144 &&& CIL.Vector.pack256 0 (-1) (-1) (-1)

theorem incomingBorrow_packed (a b c d : BitVec 64) :
    incomingBorrow (CIL.Vector.pack256 a b c d) = CIL.Vector.pack256 0 a b c := by
  exact CIL.Vector.avx2_incoming_mask a b c d

#print axioms incomingBorrow_packed

theorem incomingBorrow_align (mask : BitVec 256) :
    CIL.Vector.alignRight64 mask (BitVec.ofNat 256 0) 3 = incomingBorrow mask := by
  have aligned : CIL.Vector.alignRight64 mask 0 3 = incomingBorrow mask := by
    conv in mask => rw [← CIL.Vector.pack256_lanes mask]
    rw [CIL.Vector.avx512_incoming]
    rw [← CIL.Vector.pack256_lanes mask, incomingBorrow_packed]
    simp only [CIL.Vector.pack256_lanes]
  exact aligned

def generatedBorrow (a b : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x.ult y)) a b

theorem generatedBorrow_ternary (a b : BitVec 256) :
    CIL.Vector.map256 (fun x => x.sshiftRight 63)
      (CIL.Vector.ternaryLogic a b (CIL.Vector.zip256 (· - ·) a b) (BitVec.ofNat 8 142)) =
    generatedBorrow a b := by
  conv in a => rw [← CIL.Vector.pack256_lanes a]
  conv in b => rw [← CIL.Vector.pack256_lanes b]
  simp only [generatedBorrow, CIL.Vector.zip256]
  rw [UInt256Proof.SIMD.ternary_borrow_packed_normal]

#print axioms incomingBorrow_align
#print axioms generatedBorrow_ternary
def vectorIncomingStart : Nat := vectorBorrowStart +
  if Extracted.profile.avx512FVL then 10 else 4

/-- The selected permutation or alignment shifts each borrow to the next lane and
    clears the low lane, storing only in a fresh private home. -/
theorem vector_incoming_checked (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (maskHome : Reference) (mask : BitVec 256)
    (maskSlot : frame.locals[3]? = some (.bytes .vector256 maskHome))
    (maskRead : read current maskHome 32 1 = .ok (numberBytes mask.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ incomingHome after,
      frame.locals[4]? = some (.bytes .vector256 incomingHome) →
      read after incomingHome 32 1 = .ok (numberBytes (incomingBorrow mask).toNat 32) →
      read after maskHome 32 1 = .ok (numberBytes mask.toNat 32) →
      MemoryBelow incomingHome.allocation current after →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex vectorOutputStart args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorIncomingStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have specified : vectorSpecs[4]? = some vectorZeroSpec := by rfl
  obtain ⟨incomingHome, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector_private_store original entered current inputs outputs frame call currentCall enteredWF
      homes preserved authority 4 vectorZeroSpec specified (.v256 (incomingBorrow mask))
      (incomingBorrow mask).toNat rfl
  have order := homes.ordered 3 4 .vector256 .vector256 maskHome incomingHome (by decide) maskSlot slot
  have earlier := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_refl incomingHome.allocation) written
  have retainedMask := write_preserves_disjoint_read written maskRead (Or.inl (Nat.ne_of_lt order))
  have done := continuation incomingHome after slot loaded retainedMask earlier retained afterCall afterAuthority
    (write_extends_allocations _ _ _ _ _ written).next
  have loadMask := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 mask) mask.toNat rfl maskSlot maskRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at done in vectorOutputStart => cbv
  conv in vectorIncomingStart => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact stored _ _ _
       | exact loadMask _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_permute256, CIL.Vector.intrinsic_create256,
             CIL.Vector.intrinsic_and256, CIL.Vector.intrinsic_zero256,
             CIL.Vector.intrinsic_align256, incomingBorrow_align, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_incoming_checked

/-- Generate and shift the borrow masks while retaining every earlier private
    allocation, including the saved independent lane differences. -/
theorem vector_borrows_checked (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftHome rightHome differenceHome : Reference) (a b : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (differenceRead : read current differenceHome 32 1 =
      .ok (numberBytes (CIL.Vector.zip256 (· - ·) a b).toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ maskHome incomingHome after,
      frame.locals[3]? = some (.bytes .vector256 maskHome) →
      frame.locals[4]? = some (.bytes .vector256 incomingHome) →
      read after maskHome 32 1 = .ok (numberBytes (generatedBorrow a b).toNat 32) →
      read after incomingHome 32 1 = .ok (numberBytes (incomingBorrow (generatedBorrow a b)).toNat 32) →
      MemoryBelow maskHome.allocation current after →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex vectorOutputStart args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorBorrowStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  first
  |
    have selected : Extracted.profile.avx512FVL = false := by rfl
    apply vector_binary_checked original entered current inputs outputs frame args currentCall
      enteredWF homes authority leftHome rightHome a b leftSlot rightSlot leftRead rightRead
      vectorBorrowStart 3 (by decide) (.vector (.ltu64 256)) (generatedBorrow a b)
      (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) post
    intro maskHome middle maskSlot maskRead _ _ middlePreserved middleCall middleAuthority firstEarlier firstNext
    apply vector_incoming_checked original entered middle inputs outputs frame args call middleCall
      enteredWF homes (preserved.trans middlePreserved) middleAuthority maskHome (generatedBorrow a b) maskSlot maskRead post
    intro incomingHome after incomingSlot incomingRead retainedMask secondEarlier afterPreserved afterCall afterAuthority secondNext
    have order := homes.ordered 3 4 .vector256 .vector256 maskHome incomingHome (by decide) maskSlot incomingSlot
    exact continuation maskHome incomingHome after maskSlot incomingSlot retainedMask incomingRead
      (firstEarlier.trans (secondEarlier.weaken (Nat.le_of_lt order))) afterPreserved afterCall afterAuthority (Nat.le_trans firstNext secondNext)

  |
    have selected : Extracted.profile.avx512FVL = true := by rfl
    have specified : vectorSpecs[3]? = some vectorZeroSpec := by rfl
    obtain ⟨maskHome, middle, maskSlot, maskRead, retained, middleCall, middleAuthority, written, stored⟩ :=
      vector_private_store original entered current inputs outputs frame call currentCall enteredWF
        homes preserved authority 3 vectorZeroSpec specified (.v256 (generatedBorrow a b))
        (generatedBorrow a b).toNat rfl
    have firstEarlier := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_refl maskHome.allocation) written
    have done : ∃ fuel result returned,
        run Extracted.program fuel vectorIndex vectorIncomingStart args frame [] middle =
          .ok (result, returned) ∧ post result returned := by
      apply vector_incoming_checked original entered middle inputs outputs frame args call middleCall
        enteredWF homes retained middleAuthority maskHome (generatedBorrow a b) maskSlot maskRead post
      intro incomingHome after incomingSlot incomingRead retainedMask secondEarlier afterPreserved afterCall afterAuthority secondNext
      have order := homes.ordered 3 4 .vector256 .vector256 maskHome incomingHome (by decide) maskSlot incomingSlot
      exact continuation maskHome incomingHome after maskSlot incomingSlot retainedMask incomingRead
        (firstEarlier.trans (secondEarlier.weaken (Nat.le_of_lt order))) afterPreserved afterCall afterAuthority
        (Nat.le_trans (write_extends_allocations _ _ _ _ _ written).next secondNext)
    have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vectorBody) (args := args) (pc := pc) (stack := stack)
      .vector256 (.v256 a) a.toNat rfl leftSlot leftRead
    have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vectorBody) (args := args) (pc := pc) (stack := stack)
      .vector256 (.v256 b) b.toNat rfl rightSlot rightRead
    have loadDifference := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vectorBody) (args := args) (pc := pc) (stack := stack)
      .vector256 (.v256 (CIL.Vector.zip256 (· - ·) a b))
      (CIL.Vector.zip256 (· - ·) a b).toNat rfl differenceSlot differenceRead
    have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
    have profile : vectorBody.profile = Extracted.profile := by rfl
    conv at done in vectorIncomingStart => cbv
    conv in vectorBorrowStart => cbv
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored _ _ _
         | exact loadLeft _ _
         | exact loadRight _ _
         | exact loadDifference _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_ternary_sub256, CIL.Vector.intrinsic_reinterpret256,
               CIL.Vector.intrinsic_sign256, generatedBorrow_ternary, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_borrows_checked
end UInt256Proof.Subtract.Safety
