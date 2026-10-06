import UInt256.Methods.Add.VectorRepairMasks
import UInt256.Methods.AddSubtract.CascadeIndexExecution
import UInt256.Methods.AddSubtract.CascadeLookupExecution
import UInt256.Methods.AddSubtract.LookupRead
import CIL.Safety.CallComposition
import UInt256.Methods.AddSubtract.VectorOutputMemory

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Checked scalar index arithmetic, including both overwrites of slot seven.
    Its final mask proves the lookup index is below sixteen. -/
theorem repair_index_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (generatedHome equalHome : Reference) (generated equal : BitVec 32)
    (generatedSlot : frame.locals[0]? = some (.bytes .word32 generatedHome))
    (equalSlot : frame.locals[1]? = some (.bytes .word32 equalHome))
    (generatedRead : read current generatedHome 4 1 = .ok (numberBytes generated.toNat 4))
    (equalRead : read current equalHome 4 1 = .ok (numberBytes equal.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∀ sumHome indexHome after,
      frame.locals[0]? = some (.bytes .word32 sumHome) →
      frame.locals[1]? = some (.bytes .word32 indexHome) →
      read after sumHome 4 1 = .ok (numberBytes (equal + 2 * generated).toNat 4) →
      read after indexHome 4 1 = .ok (numberBytes (UInt256Proof.SIMD.cascadeIndex generated equal).toNat 4) →
      (UInt256Proof.SIMD.cascadeIndex generated equal).toNat < 16 →
      MemoryBelow sumHome.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel repairIndex 24 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel repairIndex 10 args frame [] current =
        .ok (result, returned) ∧ post result returned :=
  cascade_index_checked boundary entered current inputs outputs frame args currentCall enteredWF homes authority
    generatedHome equalHome generated equal generatedSlot equalSlot generatedRead equalRead post continuation

#print axioms repair_index_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose the extracted zero-argument lookup call with the checked getter.
    This includes possible first-use allocation and child-frame teardown. -/
theorem repair_lookup_call (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (post : Memory → List Value → Prop)
    (continuation : ∀ result reference,
      StaticBindingValid result lookupDescriptor reference →
      MemoryBelow memory.nextIdentity memory result →
      CallingConditions Extracted.program result inputs outputs →
      ∃ fuel final returned,
        run Extracted.program fuel repairIndex 25 args frame
          [.span (.address reference) 512] result = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel repairIndex 24 args frame [] memory =
        .ok (final, returned) ∧ post final returned :=
  cascade_lookup_call memory inputs outputs frame args call post continuation

#print axioms repair_lookup_call

/-- Execute the span-reference/native-offset/load/store sequence. The table
    entry is initialized in a private vector home before any correction write. -/
theorem repair_lookup_load (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (table indexHome : Reference) (index : BitVec 32)
    (valid : StaticBindingValid current lookupDescriptor table)
    (bound : index.toNat < 16)
    (indexSlot : frame.locals[1]? = some (.bytes .word32 indexHome))
    (indexRead : read current indexHome 4 1 = .ok (numberBytes index.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∀ correctionHome after,
      frame.locals[2]? = some (.bytes .vector256 correctionHome) →
      read after correctionHome 32 1 = .ok (numberBytes (UInt256Proof.SIMD.cascadeVector index).toNat 32) →
      MemoryBelow correctionHome.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run Extracted.program fuel repairIndex 32 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel repairIndex 25 args frame
        [.span (.address table) 512] current = .ok (final, returned) ∧ post final returned :=
  cascade_lookup_load boundary entered current inputs outputs frame args currentCall enteredWF homes authority
    table indexHome index valid bound indexSlot indexRead post continuation

#print axioms repair_lookup_load
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Store the corrected sum from a by-value argument and the initialized table
    vector, without rereading either original input. -/
theorem repair_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output correction : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[3]? = some (.reference (.address output)))
    (sumValue correctionValue : BitVec 256)
    (sumArgument : args[0]? = some (.scalar (.v256 sumValue)))
    (correctionSlot : frame.locals[2]? = some (.bytes .vector256 correction))
    (correctionRead : read current correction 32 1 = .ok (numberBytes correctionValue.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current output (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) 1 = .ok after →
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel repairIndex 38 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel repairIndex 32 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs output
      (CIL.Vector.zip256 (· + ·) sumValue correctionValue) call currentCall outputMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  have outputFormed := currentCall.output_formed outputMember
  have loadCorrection := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := repairBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 correctionValue) correctionValue.toNat rfl correctionSlot correctionRead
  have found : Extracted.program[repairIndex]? = some repairBody := by rfl
  have profile : repairBody.profile = Extracted.profile := by rfl
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact loadCorrection _ _
       | (simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, outputArgument, sumArgument, outputFormed,
           pureArity, scalars, CIL.step, CIL.Intrinsic.available, CIL.Vector.intrinsic_add256,
           checkedValue, numericValue, formValue, instruction, staticInstruction, memoryInstruction,
           storeValue, referenceAt, written, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

theorem repair_return (memory : Memory) (frame : Frame) (args : List Value)
    (sumHome : Reference) (sum : BitVec 32)
    (slot : frame.locals[0]? = some (.bytes .word32 sumHome))
    (loaded : read memory sumHome 4 1 = .ok (numberBytes sum.toNat 4)) :
    run Extracted.program 6 repairIndex 38 args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))]) := by
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := repairBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 sum) sum.toNat rfl slot loaded
  have found : Extracted.program[repairIndex]? = some repairBody := by rfl
  have returns : repairBody.returnsValue = true := by rfl
  iterate 5
    apply Eq.trans
    · apply run_next found (by rfl)
      first
      | exact loadSum _ _
      | (simp (config := { implicitDefEqProofs := false })
          [step, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : repairBody.code[43]? = some .ret := by rfl
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms repair_return
#print axioms repair_output_checked
end UInt256Proof.Add.Safety
