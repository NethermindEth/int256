import CIL.Safety.CallComposition
import UInt256.Methods.Add.CarryContract

namespace UInt256Proof.Safety

open CIL.Safety

/-- Compose a fetched carry call using the actual checked mathematical contract. -/
theorem run_carry_call {method pc : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack rest : List Value} {frame : Frame} {memory updated : Memory}
    (a b c : BitVec 64) (carryRef output : Reference) (post : Memory → List Value → Prop)
    (methodFound : Extracted.program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call Extracted.addWithCarryIndex
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carryRef), .reference (.address output)] rest updated))
    (wellFormed : updated.WellFormed) (incoming : c.toNat ≤ 1)
    (carryReadable : read updated carryRef 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access updated carryRef 8 1 true = .ok ())
    (outputWritable : access updated output 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryRef output)
    (continuation : ∀ stored, CarryPost a b c carryRef output updated stored →
      ∃ fuel result values,
        run Extracted.program fuel method (pc + 1) args frame rest stored = .ok (result, values) ∧
        post result values) :
    ∃ fuel result values,
      run Extracted.program fuel method pc args frame stack memory = .ok (result, values) ∧
      post result values := by
  obtain ⟨childFuel, stored, invoked, guarantees⟩ := carry_checked_contract a b c carryRef output updated
    wellFormed incoming carryReadable carryWritable outputWritable disjoint
  obtain ⟨parentFuel, result, values, resumed, satisfied⟩ := continuation stored guarantees
  have resumed' : run Extracted.program parentFuel method (pc + 1) args frame ([] ++ rest) stored =
      .ok (result, values) := resumed
  obtain ⟨fuel, finished⟩ := run_call_exists methodFound instructionFound stepped
    ⟨childFuel, invoked⟩ ⟨parentFuel, resumed'⟩
  exact ⟨fuel, result, values, finished, satisfied⟩

#print axioms run_carry_call

end UInt256Proof.Safety
