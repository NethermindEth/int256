import UInt256.Methods.AddSubtract.Vector128Memory
import CIL.Safety.StepComposition

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

def vector128OperandLocal (right upper : Bool) : Nat :=
  (if right then 2 else 0) + (if upper then 1 else 0)

def vector128OperandLoad (right upper : Bool) : Nat :=
  if right then (if upper then 20 else 15) else (if upper then 12 else 8)

def vector128ZeroSpec : NumericLocalSpec := ⟨.vector128, .v128 0, 0, rfl⟩

/-- Each actual half-load/private-store pair captures initial caller bytes.
    The preceding address-producing instructions must separately establish the
    stack reference; the load checks the complete 16-byte access. -/
theorem vector128_operand_checked (original entered current : Memory)
    (inputs outputs : List Reference) (input : Reference) (frame : Frame)
    (root : LocalSlot) (slots : List LocalSlot) (args rest : List Value)
    (layout : frame.locals = root :: slots)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : input ∈ inputs) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (right upper : Bool)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[vector128OperandLocal right upper + 1]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok
        (numberBytes (inputHalf original input (if upper then 1 else 0)).toNat 16) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (inputHalf original input (if upper then 1 else 0)).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (vector128OperandLoad right upper + 2)
          args frame rest after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (vector128OperandLoad right upper) args frame
        (.reference (.address { input with offset := input.offset + 16 * (if upper then 1 else 0) }) :: rest)
        current = .ok (result, returned) ∧ post result returned := by
  have specified : vector128Specs[vector128OperandLocal right upper]? = some vector128ZeroSpec := by
    cases right <;> cases upper <;> rfl
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store original.nextIdentity entered current inputs outputs frame root slots
      layout currentCall enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (inputHalf original input (if upper then 1 else 0)))
      (inputHalf original input (if upper then 1 else 0)).toNat rfl
  have done := continuation reference after slot loaded (preserved.trans retained) afterCall afterAuthority written
  have reading := vector128_input_load original current inputs outputs input
    (if upper then 1 else 0) call currentCall member preserved
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  cases right <;> cases upper <;>
    simp only [vector128OperandLoad, vector128OperandLocal, Bool.false_eq_true, ite_false, ite_true,
      Fin.val_zero, Fin.val_one] at stored reading done ⊢
  all_goals
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at reading
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, staticInstruction, memoryInstruction, reading, checkedAt, Except.mapError,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_operand_checked
end UInt256Proof.AddSubtract.Safety
