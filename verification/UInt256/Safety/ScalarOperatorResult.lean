import UInt256.Safety.ScalarOperatorContract

namespace UInt256Model.Safety

/-- Replace the internal Boolean calculation with an independently proved public
    predicate, preserving the same checked invocation and caller memory. -/
theorem ScalarOperatorContract.result_congr {α : Type} {first negate : Bool}
    {encode : α → CIL.Value} {operation desired : BitVec 256 → α → Bool}
    {program : CIL.Program} {method : Nat}
    (meaning : ∀ input word, (operation input word != negate) = desired input word)
    (proof : ScalarOperatorContract first negate encode operation program method) :
    ScalarOperatorContract first false encode desired program method := by
  intro memory input word call
  obtain ⟨fuel, final, certificate, cells⟩ := proof memory input word call
  have positive (flag : Bool) : (flag != false) = flag := by cases flag <;> rfl
  exact ⟨fuel, final, by simpa only [meaning, positive] using certificate, cells⟩

#print axioms ScalarOperatorContract.result_congr
end UInt256Model.Safety
