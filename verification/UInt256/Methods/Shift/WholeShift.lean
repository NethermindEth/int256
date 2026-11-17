import UInt256.Methods.Shift.ExtractLemmas
import UInt256.Methods.Shift.Limbs

namespace UInt256Proof.Shift

theorem left_words_zero (a0 a1 a2 a3 : BitVec 64) (count : Nat) (bound : count < 64) :
    pack a0 a1 a2 a3 <<< count =
      pack (a0 <<< count) ((a1 <<< count) ||| (a0 >>> (64 - count)))
        ((a2 <<< count) ||| (a1 >>> (64 - count)))
        ((a3 <<< count) ||| (a2 >>> (64 - count))) := by
  apply eq_of_words
  · rw [left_extract_low _ _ (by decide), pack_extract_zero, pack_extract_zero]
  · rw [left_extract_word _ _ _ (by decide) (by decide) bound,
      pack_extract_one, pack_extract_one]
    simp only [show 64 - 64 = 0 from rfl, pack_extract_zero]
  · rw [left_extract_word _ _ _ (by decide) (by decide) bound,
      pack_extract_two, pack_extract_two]
    simp only [show 128 - 64 = 64 from rfl, pack_extract_one]
  · rw [left_extract_word _ _ _ (by decide) (by decide) bound,
      pack_extract_three, pack_extract_three]
    simp only [show 192 - 64 = 128 from rfl, pack_extract_two]

theorem right_words_zero (a0 a1 a2 a3 : BitVec 64) (count : Nat) (bound : count < 64) :
    pack a0 a1 a2 a3 >>> count =
      pack ((a0 >>> count) ||| (a1 <<< (64 - count)))
        ((a1 >>> count) ||| (a2 <<< (64 - count)))
        ((a2 >>> count) ||| (a3 <<< (64 - count))) (a3 >>> count) := by
  apply eq_of_words
  · rw [right_extract_word _ _ _ bound, pack_extract_zero, pack_extract_zero]
    simp only [show 0 + 64 = 64 from rfl, pack_extract_one]
  · rw [right_extract_word _ _ _ bound, pack_extract_one, pack_extract_one]
    simp only [show 64 + 64 = 128 from rfl, pack_extract_two]
  · rw [right_extract_word _ _ _ bound, pack_extract_two, pack_extract_two]
    simp only [show 128 + 64 = 192 from rfl, pack_extract_three]
  · rw [right_extract_word _ _ _ bound, pack_extract_three, pack_extract_three]
    simp only [show 192 + 64 = 256 from rfl,
      extract_beyond (pack a0 a1 a2 a3) 256 (by decide)]
    simp


theorem left_move_one (a0 a1 a2 a3 : BitVec 64) :
    pack a0 a1 a2 a3 <<< 64 = pack 0 a0 a1 a2 := by
  apply eq_of_words
  · rw [left_extract_zero _ _ _ (by decide), pack_extract_zero]
  · rw [left_extract_move _ _ _ (by decide) (by decide), pack_extract_one]
    exact pack_extract_zero a0 a1 a2 a3
  · rw [left_extract_move _ _ _ (by decide) (by decide), pack_extract_two]
    exact pack_extract_one a0 a1 a2 a3
  · rw [left_extract_move _ _ _ (by decide) (by decide), pack_extract_three]
    exact pack_extract_two a0 a1 a2 a3

theorem left_move_two (a0 a1 a2 a3 : BitVec 64) :
    pack a0 a1 a2 a3 <<< 128 = pack 0 0 a0 a1 := by
  apply eq_of_words
  · rw [left_extract_zero _ _ _ (by decide), pack_extract_zero]
  · rw [left_extract_zero _ _ _ (by decide), pack_extract_one]
  · rw [left_extract_move _ _ _ (by decide) (by decide), pack_extract_two]
    exact pack_extract_zero a0 a1 a2 a3
  · rw [left_extract_move _ _ _ (by decide) (by decide), pack_extract_three]
    exact pack_extract_one a0 a1 a2 a3

theorem left_move_three (a0 a1 a2 a3 : BitVec 64) :
    pack a0 a1 a2 a3 <<< 192 = pack 0 0 0 a0 := by
  apply eq_of_words
  · rw [left_extract_zero _ _ _ (by decide), pack_extract_zero]
  · rw [left_extract_zero _ _ _ (by decide), pack_extract_one]
  · rw [left_extract_zero _ _ _ (by decide), pack_extract_two]
  · rw [left_extract_move _ _ _ (by decide) (by decide), pack_extract_three]
    exact pack_extract_zero a0 a1 a2 a3

theorem right_move_one (a0 a1 a2 a3 : BitVec 64) :
    pack a0 a1 a2 a3 >>> 64 = pack a1 a2 a3 0 := by
  apply eq_of_words
  · rw [right_extract_move, pack_extract_zero]
    exact pack_extract_one a0 a1 a2 a3
  · rw [right_extract_move, pack_extract_one]
    exact pack_extract_two a0 a1 a2 a3
  · rw [right_extract_move, pack_extract_two]
    exact pack_extract_three a0 a1 a2 a3
  · rw [right_extract_move, pack_extract_three]
    exact extract_beyond (pack a0 a1 a2 a3) 256 (by decide)

theorem right_move_two (a0 a1 a2 a3 : BitVec 64) :
    pack a0 a1 a2 a3 >>> 128 = pack a2 a3 0 0 := by
  apply eq_of_words
  · rw [right_extract_move, pack_extract_zero]
    exact pack_extract_two a0 a1 a2 a3
  · rw [right_extract_move, pack_extract_one]
    exact pack_extract_three a0 a1 a2 a3
  · rw [right_extract_move, pack_extract_two]
    exact extract_beyond (pack a0 a1 a2 a3) 256 (by decide)
  · rw [right_extract_move, pack_extract_three]
    exact extract_beyond (pack a0 a1 a2 a3) 320 (by decide)

theorem right_move_three (a0 a1 a2 a3 : BitVec 64) :
    pack a0 a1 a2 a3 >>> 192 = pack a3 0 0 0 := by
  apply eq_of_words
  · rw [right_extract_move, pack_extract_zero]
    exact pack_extract_three a0 a1 a2 a3
  · rw [right_extract_move, pack_extract_one]
    exact extract_beyond (pack a0 a1 a2 a3) 256 (by decide)
  · rw [right_extract_move, pack_extract_two]
    exact extract_beyond (pack a0 a1 a2 a3) 320 (by decide)
  · rw [right_extract_move, pack_extract_three]
    exact extract_beyond (pack a0 a1 a2 a3) 384 (by decide)

theorem left_words_one (a0 a1 a2 a3 : BitVec 64) (count : Nat)
    (bound : count < 64) :
    pack a0 a1 a2 a3 <<< (64 + count) =
      pack 0 (a0 <<< count) ((a1 <<< count) ||| (a0 >>> (64 - count))) ((a2 <<< count) ||| (a1 >>> (64 - count))) := by
  rw [BitVec.shiftLeft_add, left_move_one, left_words_zero _ _ _ _ count bound]
  simp

theorem left_words_two (a0 a1 a2 a3 : BitVec 64) (count : Nat)
    (bound : count < 64) :
    pack a0 a1 a2 a3 <<< (128 + count) =
      pack 0 0 (a0 <<< count) ((a1 <<< count) ||| (a0 >>> (64 - count))) := by
  rw [BitVec.shiftLeft_add, left_move_two, left_words_zero _ _ _ _ count bound]
  simp

theorem left_words_three (a0 a1 a2 a3 : BitVec 64) (count : Nat)
    (bound : count < 64) :
    pack a0 a1 a2 a3 <<< (192 + count) =
      pack 0 0 0 (a0 <<< count) := by
  rw [BitVec.shiftLeft_add, left_move_three, left_words_zero _ _ _ _ count bound]
  simp

theorem right_words_one (a0 a1 a2 a3 : BitVec 64) (count : Nat)
    (bound : count < 64) :
    pack a0 a1 a2 a3 >>> (64 + count) =
      pack ((a1 >>> count) ||| (a2 <<< (64 - count))) ((a2 >>> count) ||| (a3 <<< (64 - count))) (a3 >>> count) 0 := by
  rw [right_add, right_move_one, right_words_zero _ _ _ _ count bound]
  simp

theorem right_words_two (a0 a1 a2 a3 : BitVec 64) (count : Nat)
    (bound : count < 64) :
    pack a0 a1 a2 a3 >>> (128 + count) =
      pack ((a2 >>> count) ||| (a3 <<< (64 - count))) (a3 >>> count) 0 0 := by
  rw [right_add, right_move_two, right_words_zero _ _ _ _ count bound]
  simp

theorem right_words_three (a0 a1 a2 a3 : BitVec 64) (count : Nat)
    (bound : count < 64) :
    pack a0 a1 a2 a3 >>> (192 + count) =
      pack (a3 >>> count) 0 0 0 := by
  rw [right_add, right_move_three, right_words_zero _ _ _ _ count bound]
  simp

end UInt256Proof.Shift
