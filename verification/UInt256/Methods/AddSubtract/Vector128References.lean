import UInt256.Methods.AddSubtract.Vector128Operands

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

def vector128SavedFrame (frame : Frame) (slots : List LocalSlot) (right : Reference) : Frame :=
  { frame with locals := .root (some (.address right)) :: slots }

/-- Both input references pass the checked formation operations before the
    right reference is saved in its root and the left one is duplicated. -/
theorem vector128_reference_prefix (memory : Memory) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (initial : Option ManagedReference)
    (layout : frame.locals = .root initial :: slots) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (leftFormed : form memory left = .ok left)
    (rightFormed : form memory right = .ok right)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index 8 args (vector128SavedFrame frame slots right)
        [.reference (.address left), .reference (.address left)] memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] memory = .ok (result, returned) ∧
      post result returned := by
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, leftArg, rightArg, checkedValue, formValue, leftFormed, rightFormed,
           staticInstruction, memoryInstruction, storeLocal, layout, vector128SavedFrame,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The extracted signed offset computes the upper half within the live input
    allocation and its permitted view, before any load is attempted. -/
theorem vector128_left_upper (memory : Memory) (inputs outputs : List Reference)
    (left : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (member : left ∈ inputs) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index 12 args frame
        [.reference (.address { left with offset := left.offset + 16 })] memory =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 10 args frame [.reference (.address left)] memory =
        .ok (result, returned) ∧ post result returned := by
  have advanced := call.input_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at advanced
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, staticInstruction, memoryInstruction, CIL.offsetValue, referenceAt, advanced,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Reload the tracked right-input root and, for the upper half, perform the
    checked offset instruction before the next vector load. -/
theorem vector128_right_reference (memory : Memory) (inputs outputs : List Reference)
    (right : Reference) (frame : Frame) (args : List Value)
    (slot : frame.locals[0]? = some (.root (some (.address right))))
    (call : CallingConditions Extracted.program memory inputs outputs)
    (member : right ∈ inputs) (upper : Bool) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (if upper then 20 else 15) args frame
        [.reference (.address { right with offset := right.offset + 16 * (if upper then 1 else 0) })] memory =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (if upper then 17 else 14) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have formed := call.input_formed member
  have advanced := call.input_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at advanced
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.mul_zero,
    Nat.mul_one, Nat.add_zero] at continuation ⊢
  all_goals
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, slot, loadLocal, formValue, formed, staticInstruction, memoryInstruction,
             CIL.offsetValue, referenceAt, advanced, checkedAt, Except.mapError,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_reference_prefix
#print axioms vector128_left_upper
#print axioms vector128_right_reference
end UInt256Proof.AddSubtract.Safety
