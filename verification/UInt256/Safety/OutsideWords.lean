import CIL.Safety.MethodContract

namespace UInt256Proof
open CIL.Safety

/-- A byte outside two words is outside their two-entry contract footprint. -/
theorem outside_words {first second : Reference} {id offset : Nat}
    (outFirst : OutsideWord first id offset) (outSecond : OutsideWord second id offset) :
    Outside [(first, 8), (second, 8)] id offset := by
  intro entry member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact outFirst
  · exact outSecond

#print axioms outside_words
end UInt256Proof
