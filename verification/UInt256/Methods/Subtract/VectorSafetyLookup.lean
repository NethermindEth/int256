import UInt256.Methods.AddSubtract.CascadeLookupExecution
import UInt256.Methods.Subtract.VectorSafetyIndex
import UInt256.Methods.AddSubtract.LookupRead
import CIL.Safety.CallComposition

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose the extracted zero-argument lookup call with the checked getter.
    This includes possible first-use allocation and child-frame teardown. -/
theorem vector_lookup_call (memory : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program memory inputs outputs)
    (post : Memory → List Value → Prop)
    (continuation : ∀ result reference,
      StaticBindingValid result lookupDescriptor reference →
      MemoryBelow memory.nextIdentity memory result →
      CallingConditions Extracted.program result inputs outputs →
      ∃ fuel final returned,
        run Extracted.program fuel vectorIndex (vectorTestStart + 27) args frame
          [.span (.address reference) 512] result = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 26) args frame [] memory =
        .ok (final, returned) ∧ post final returned :=
  cascade_lookup_call memory inputs outputs frame args call post continuation

#print axioms vector_lookup_call

/-- Execute the span-reference/native-offset/load/store sequence. The table
    entry is initialized in a private vector home before any correction write. -/
theorem vector_lookup_load (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (table indexHome : Reference) (index : BitVec 32)
    (valid : StaticBindingValid current lookupDescriptor table)
    (bound : index.toNat < 16)
    (indexSlot : frame.locals[7]? = some (.bytes .word32 indexHome))
    (indexRead : read current indexHome 4 1 = .ok (numberBytes index.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∀ correctionHome after,
      frame.locals[8]? = some (.bytes .vector256 correctionHome) →
      read after correctionHome 32 1 = .ok (numberBytes (UInt256Proof.SIMD.cascadeVector index).toNat 32) →
      MemoryBelow correctionHome.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run Extracted.program fuel vectorIndex (vectorTestStart + 34) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 27) args frame
        [.span (.address table) 512] current = .ok (final, returned) ∧ post final returned :=
  cascade_lookup_load boundary entered current inputs outputs frame args currentCall enteredWF homes authority
    table indexHome index valid bound indexSlot indexRead post continuation

#print axioms vector_lookup_load
end UInt256Proof.Subtract.Safety
