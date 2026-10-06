import UInt256.Methods.AddSubtract.CascadeIndexExecution
import UInt256.Methods.AddSubtract.LookupRead
import CIL.Safety.CallComposition

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

def cascadeCorrectionSlot : Nat := match cascadeBody.code[cascadeStart+21]? with
  | some (.setLocal index) => index | _ => 0

def cascadeVectorZero : NumericLocalSpec := ⟨.vector256, .v256 0, 0, rfl⟩

/-- Compose the extracted zero-argument lookup call with the checked getter.
    This includes possible first-use allocation and child-frame teardown. -/
theorem cascade_lookup_call (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (post : Memory → List Value → Prop)
    (continuation : ∀ result reference,
      StaticBindingValid result lookupDescriptor reference →
      MemoryBelow memory.nextIdentity memory result →
      CallingConditions Extracted.program result inputs outputs →
      ∃ fuel final returned,
        run Extracted.program fuel cascadeMethodIndex (cascadeStart + 15) args frame
          [.span (.address reference) 512] result = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel cascadeMethodIndex (cascadeStart + 14) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨result, reference, invoked, valid, preserved, afterCall⟩ := lookup_getter_checked memory inputs outputs call
  obtain ⟨fuel, final, returned, tail, satisfied⟩ := continuation result reference valid preserved afterCall
  have found : Extracted.program[cascadeMethodIndex]? = some cascadeBody := by rfl
  have fetched : cascadeBody.code[cascadeStart + 14]? = some (.call lookupIndex 0) := by rfl
  have stepped : step cascadeBody (.call lookupIndex 0) (cascadeStart + 14) args frame [] memory =
      .ok (.call lookupIndex [] [] memory) := by rfl
  obtain ⟨combined, executed⟩ := run_call_exists found fetched stepped ⟨4, invoked⟩ ⟨fuel, tail⟩
  exact ⟨combined, final, returned, executed, satisfied⟩

#print axioms cascade_lookup_call

/-- Execute the span-reference/native-offset/load/store sequence. The table
    entry is initialized in a private vector home before any correction write. -/
theorem cascade_lookup_load (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary cascadeSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (table indexHome : Reference) (index : BitVec 32)
    (valid : StaticBindingValid current lookupDescriptor table)
    (bound : index.toNat < 16)
    (indexSlot : frame.locals[cascadeIndexSlot]? = some (.bytes .word32 indexHome))
    (indexRead : read current indexHome 4 1 = .ok (numberBytes index.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∀ correctionHome after,
      frame.locals[cascadeCorrectionSlot]? = some (.bytes .vector256 correctionHome) →
      read after correctionHome 32 1 = .ok (numberBytes (UInt256Proof.SIMD.cascadeVector index).toNat 32) →
      MemoryBelow correctionHome.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run Extracted.program fuel cascadeMethodIndex (cascadeStart + 22) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel cascadeMethodIndex (cascadeStart + 15) args frame
        [.span (.address table) 512] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨correctionHome, after, slot, readback, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store Extracted.program cascadeBody cascadeSpecs boundary entered current inputs outputs frame currentCall enteredWF homes authority
      cascadeCorrectionSlot cascadeVectorZero (by rfl) (.v256 (UInt256Proof.SIMD.cascadeVector index))
      (UInt256Proof.SIMD.cascadeVector index).toNat rfl
  have earlier := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_refl correctionHome.allocation) written
  have done := continuation correctionHome after slot readback earlier preserved afterCall afterAuthority
  have loadIndex := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := cascadeBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 index) index.toNat rfl indexSlot indexRead
  obtain ⟨offset, loaded⟩ := lookup_vector_read current table index currentCall.1.1 valid bound
  have widened : index.setWidth 64 = BitVec.ofNat 64 index.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [← widened] at offset
  have formed := valid.reference_valid
  have widen : (index.zeroExtend 64).toNat = index.toNat := by
    rw [BitVec.zeroExtend_eq_setWidth]
    exact BitVec.toNat_setWidth_of_le (by decide)
  have found : Extracted.program[cascadeMethodIndex]? = some cascadeBody := by rfl
  conv at done in cascadeStart => cbv
  conv in cascadeStart => cbv
  have indexIndex : cascadeIndexSlot = cascadeIndexSlot := rfl
  conv at indexIndex => rhs; cbv
  have correctionIndex : cascadeCorrectionSlot = cascadeCorrectionSlot := rfl
  conv at correctionIndex => rhs; cbv
  simp only [indexIndex, correctionIndex] at *
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact stored _ _ _
       | exact loadIndex _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, pureArity, scalars, CIL.step, staticInstruction, memoryInstruction,
             CIL.offsetValue, widen, offset, loaded, referenceAt, formValue, formed,
             checkedValue, numericValue, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms cascade_lookup_load
end UInt256Proof.AddSubtract.Safety
