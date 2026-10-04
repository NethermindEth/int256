import UInt256.Methods.Multiply.CountCarry
open CIL
namespace UInt256Proof.Multiply

def columnStep (state : W64 × W64) (word : W64) : W64 × W64 :=
  (state.1 + word, countCarry state.1 word state.2)

def column (start : W64) (words : List W64) : W64 × W64 :=
  words.foldl columnStep (start, 0)

theorem sum_words_nat (words : List W64) :
    words.sum.toNat = (words.map BitVec.toNat).sum % 2^64 := by
  induction words with
  | nil => simp
  | cons word words induction =>
    simp only [List.sum_cons, BitVec.toNat_add, induction, List.map_cons, Nat.add_mod_mod]

theorem column_fold (words : List W64) (start count : W64)
    (bound : count.toNat + words.length < 2^64) :
    (words.foldl columnStep (start, count)).1.toNat +
        2^64 * (words.foldl columnStep (start, count)).2.toNat =
      start.toNat + 2^64 * count.toNat + (words.map BitVec.toNat).sum := by
  induction words generalizing start count with
  | nil => simp
  | cons word words induction =>
    have nextCount := countCarry_nat start word count (by
      simp only [List.length_cons] at bound
      omega)
    have nextBound := sumHigh_bound start word
    have next := induction (start + word) (countCarry start word count) (by
      simp only [List.length_cons] at bound
      omega)
    have sum := sum_decomposition start word
    simp only [List.foldl_cons, columnStep, List.map_cons, List.sum_cons] at next ⊢
    omega

theorem column_correct (start : W64) (words : List W64) (bound : words.length < 2^64) :
    (column start words).1.toNat + 2^64 * (column start words).2.toNat =
      start.toNat + (words.map BitVec.toNat).sum := by
  simpa [column] using column_fold words start 0 (by simpa using bound)

end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.column_correct
