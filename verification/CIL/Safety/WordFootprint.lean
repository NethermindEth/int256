import CIL.Safety.WordMemory

namespace CIL.Safety

def WordsDisjoint (left right : Reference) : Prop :=
  left.allocation ≠ right.allocation ∨ left.offset + 8 ≤ right.offset ∨ right.offset + 8 ≤ left.offset

def OutsideWord (reference : Reference) (id offset : Nat) : Prop :=
  id ≠ reference.allocation ∨ offset < reference.offset ∨ reference.offset + 8 ≤ offset

theorem write_word_outside {memory result : Memory} {reference : Reference} {word : BitVec 64}
    (written : write memory reference (numberBytes word.toNat 8) 1 = .ok result)
    (id offset : Nat) (outside : OutsideWord reference id offset) :
    result.cells id offset = memory.cells id offset := by
  apply write_outside _ _ _ _ _ _ _ written
  simpa only [OutsideWord, numberBytes, List.length_map, List.length_range] using outside

#print axioms write_word_outside

end CIL.Safety
