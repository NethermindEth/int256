import UInt256.Methods.AddSubtract.VectorBinary

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Execute the extracted independent lane subtraction and its private result
    store while retaining both input snapshots for borrow detection. -/
theorem vector_difference_checked (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftHome rightHome : Reference) (a b : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ resultHome after,
      frame.locals[2]? = some (.bytes .vector256 resultHome) →
      read after resultHome 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· - ·) a b).toNat 32) →
      read after leftHome 32 1 = .ok (numberBytes a.toNat 32) →
      read after rightHome 32 1 = .ok (numberBytes b.toNat 32) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOperandStart + 12) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOperandStart + 8) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  apply vector_binary_checked original entered current inputs outputs frame args currentCall
    enteredWF homes authority leftHome rightHome a b leftSlot rightSlot leftRead rightRead
    (vectorOperandStart + 8) 2 (by decide) (.vector (.sub64 256))
    (CIL.Vector.zip256 (· - ·) a b) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) post
  intro resultHome after slot loaded retainedLeft retainedRight retained afterCall afterAuthority _ advanced
  exact continuation resultHome after slot loaded retainedLeft retainedRight (preserved.trans retained) afterCall afterAuthority advanced

#print axioms vector_difference_checked

/-- The common output suffix starts at the output argument preceding SkipInit,
    independently of the selected ISA borrow computation. -/
def vectorOutputStart : Nat := (vectorBody.code.findIdx fun op =>
  match op with | .skipInit => true | _ => false) - 1

/-- Discover the selected ISA's borrow block from its actual intrinsic. -/
def vectorBorrowStart : Nat := if Extracted.profile.avx512FVL then
  (vectorBody.code.findIdx fun op => match op with
    | .intrinsic (.avx512 .ternaryLogic) 4 => true | _ => false) - 4
else
  (vectorBody.code.findIdx fun op => match op with
    | .intrinsic (.vector (.ltu64 256)) 2 => true | _ => false) - 2

theorem vector_borrow_dispatch (memory : Memory) (frame : Frame) (args : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorBorrowStart args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOperandStart + 12) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at continuation in vectorBorrowStart => cbv
  conv in vectorOperandStart => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector_borrow_dispatch
end UInt256Proof.Subtract.Safety
