import CIL.Embedding.Tactic
import CIL.Safety.Embedding.Simulation
import UInt256.Safety.Contract
import UInt256.Safety.AggregateReturn
import UInt256.Safety.OrderedScalarContract

/-!
Public contracts proved over `program.set index expected` hold for `program` when
`expected` embeds into its method `index`; the contract statements are unchanged.
-/

namespace UInt256Model.Safety

open CIL.Safety

/-- An embedded body keeps the program's static descriptors, so caller conditions carry over. -/
theorem CallingConditions.of_embeds {program : CIL.Program} {index : Nat} {expected : CIL.Method}
    (bound : CIL.MethodEmbeds program index expected) {memory : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) :
    CallingConditions (program.set index expected) memory inputs outputs :=
  ⟨call.1, by rw [bound.descriptors]; exact call.2⟩

theorem WrappingBinaryContract.of_embeds {operation : BitVec 256 → BitVec 256 → BitVec 256}
    {program : CIL.Program} {index method : Nat} {expected : CIL.Method}
    (bound : CIL.MethodEmbeds program index expected)
    (contract : WrappingBinaryContract operation (program.set index expected) method) :
    WrappingBinaryContract operation program method := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, rest⟩ := contract memory left right output (call.of_embeds bound)
  exact ⟨fuel, final, bound.certificate certificate, rest⟩

theorem AggregateReturn.BinaryContract.of_embeds {operation : BitVec 256 → BitVec 256 → BitVec 256}
    {program : CIL.Program} {index method : Nat} {expected : CIL.Method}
    (bound : CIL.MethodEmbeds program index expected)
    (contract : AggregateReturn.BinaryContract operation (program.set index expected) method) :
    AggregateReturn.BinaryContract operation program method := by
  intro memory left right call
  obtain ⟨fuel, final, bytes, certificate, rest⟩ := contract memory left right (call.of_embeds bound)
  exact ⟨fuel, final, bytes, bound.certificate certificate, rest⟩

theorem OrderedScalarContract.of_embeds {α : Type} {scalarFirst : Bool} {encode : α → CIL.Value}
    {operation : BitVec 256 → α → CIL.Value} {program : CIL.Program} {index method : Nat} {expected : CIL.Method}
    (bound : CIL.MethodEmbeds program index expected)
    (contract : OrderedScalarContract scalarFirst encode operation (program.set index expected) method) :
    OrderedScalarContract scalarFirst encode operation program method := by
  intro memory input scalar call
  obtain ⟨fuel, final, certificate, rest⟩ := contract memory input scalar (call.of_embeds bound)
  exact ⟨fuel, final, bound.certificate certificate, rest⟩

#print axioms CallingConditions.of_embeds
#print axioms WrappingBinaryContract.of_embeds
#print axioms AggregateReturn.BinaryContract.of_embeds
#print axioms OrderedScalarContract.of_embeds

end UInt256Model.Safety
