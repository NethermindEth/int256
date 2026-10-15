import CIL.Safety.ArgumentHomeValues
import CIL.Safety.ByteEncoding
import UInt256.Safety.Calling

namespace UInt256Model.Safety

open CIL.Safety

/-- A completely initialized private argument copy denotes the original value. -/
theorem inputValue_of_encoded_read {memory : Memory} {reference : Reference}
    {bits : BitVec 256}
    (loaded : read memory reference 32 1 = .ok (numberBytes bits.toNat 32)) :
    inputValue memory reference = bits := by
  have snapshot := read_result_snapshot loaded
  have encoded := congrArg CIL.Safety.byteNumber snapshot
  rw [byteNumber_numberBytes,
    byteNumber_snapshot (fun offset => (memory.cells reference.allocation offset).bits)
      reference.offset 32] at encoded
  have bound : bits.toNat < 256^32 := bits.isLt
  rw [Nat.mod_eq_of_lt bound] at encoded
  unfold inputValue byteValue
  rw [← encoded]
  simp

#print axioms inputValue_of_encoded_read

/-- A proved initialized copy can be passed as an additional read-only input. -/
theorem CallingConditions.with_readable_input {program : CIL.Program}
    {memory : Memory} {inputs outputs : List Reference} {reference : Reference}
    (call : CallingConditions program memory inputs outputs)
    {bytes : List (BitVec 8)} (loaded : read memory reference 32 1 = .ok bytes) :
    CallingConditions program memory (inputs ++ [reference]) outputs := by
  refine ⟨⟨call.1.1, ?_, call.1.2.2⟩, call.2⟩
  intro view member
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_singleton] at member
  rcases member with member | rfl
  · exact call.1.2.1 view member
  · exact ⟨bytes, loaded⟩

#print axioms CallingConditions.with_readable_input

end UInt256Model.Safety
