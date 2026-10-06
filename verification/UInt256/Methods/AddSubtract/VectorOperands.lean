import UInt256.Methods.AddSubtract.VectorMemory
import CIL.Safety.StepComposition

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

def vectorOperandStart : Nat := vectorBody.code.findIdx fun op =>
  match op with | .arg 0 => true | _ => false

def vectorZeroSpec : NumericLocalSpec := ⟨.vector256, .v256 0, 0, rfl⟩

/-- Execute the actual load/bitcast/private-store block for either operand.
    Its value is the original caller snapshot even after earlier local writes. -/
theorem vector_operand_checked (original entered current : Memory)
    (inputs outputs : List Reference) (input : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : input ∈ inputs) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (second : Bool)
    (argument : args[if second then 1 else 0]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if second then 1 else 0]? = some (.bytes .vector256 reference) →
      read after reference 32 1 = .ok (numberBytes (inputValue original input).toNat 32) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (inputValue original input).toNat 32) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOperandStart + (if second then 4 else 0) + 4)
          args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOperandStart + (if second then 4 else 0))
        args frame [] current = .ok (result, returned) ∧ post result returned := by
  have specified : vectorSpecs[if second then 1 else 0]? = some vectorZeroSpec := by
    cases second <;> rfl
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector_private_store original entered current inputs outputs frame call currentCall enteredWF
      homes preserved authority _ vectorZeroSpec specified (.v256 (inputValue original input))
      (inputValue original input).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have formed := currentCall.input_formed member
  have reading : loadValue current (.address input) 32 = .ok (.v256 (inputValue original input)) := by
    rw [currentCall.input_load member]
    simp only [inputValue, call.input_bytes_of_memory_below preserved member]
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  cases second <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at argument stored done ⊢
  all_goals
    conv at done in vectorOperandStart => cbv
    conv in vectorOperandStart => cbv
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, formValue, formed, reading,
               staticInstruction, memoryInstruction, checkedAt, Except.mapError, Bind.bind, Except.bind,
               Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_operand_checked

/-- Both input snapshots are initialized in distinct private homes before
    lane arithmetic; arbitrary overlap among caller references is retained. -/
theorem vector_operands_checked (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vectorBody args original = .ok (frame, entered))
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArgument : args[0]? = some (.reference (.address left)))
    (rightArgument : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ leftHome rightHome after,
      frame.locals[0]? = some (.bytes .vector256 leftHome) →
      frame.locals[1]? = some (.bytes .vector256 rightHome) →
      leftHome.allocation < rightHome.allocation →
      read after leftHome 32 1 = .ok (numberBytes (inputValue original left).toNat 32) →
      read after rightHome 32 1 = .ok (numberBytes (inputValue original right).toNat 32) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOperandStart + 8) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorOperandStart args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have authority : AccessBelow entered.nextIdentity entered entered := (MemoryBelow.refl _ _).accessBelow
  apply vector_operand_checked original entered entered inputs outputs left frame args call enteredCall
    leftMember enteredCall.1.1 homes preserved authority false leftArgument post
  intro leftHome middle leftSlot leftRead middlePreserved middleCall middleAuthority firstWrite
  apply vector_operand_checked original entered middle inputs outputs right frame args call middleCall
    rightMember enteredCall.1.1 homes middlePreserved middleAuthority true rightArgument post
  intro rightHome after rightSlot rightRead afterPreserved afterCall afterAuthority written
  have order := homes.ordered 0 1 .vector256 .vector256 leftHome rightHome (by decide) leftSlot rightSlot
  have retained := write_preserves_disjoint_read written leftRead (Or.inl (Nat.ne_of_lt order))
  exact continuation leftHome rightHome after leftSlot rightSlot order retained rightRead
    afterPreserved afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ written).next)

#print axioms vector_operands_checked

/-- Follow any extracted ISA guard before the operand-loading block. -/
theorem vector_operand_dispatch (memory : Memory) (frame : Frame) (args : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorOperandStart args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex 0 args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at continuation in vectorOperandStart => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           checkedValue, numericValue, checkedAt, Except.mapError, Bind.bind, Except.bind,
           Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector_operand_dispatch
end UInt256Proof.AddSubtract.Safety
