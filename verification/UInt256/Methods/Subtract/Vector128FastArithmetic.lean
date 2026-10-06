import UInt256.Methods.Subtract.Vector128Dispatch
import UInt256.Arithmetic.SIMDBorrow
import UInt256.Safety.HalfRepresentation
import UInt256.Methods.Subtract.BorrowArithmetic

namespace UInt256Proof.Subtract.Safety
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The checked branch expression is exactly the independent arithmetic
    propagation test over the original input limbs. -/
theorem vector128_initial_propagation (memory : Memory) (left right : Reference) :
    vector128InitialPropagation memory left right =
      UInt256Proof.propagation128 (inputLimb memory left) (inputLimb memory right) := by
  simp [vector128InitialPropagation, vector128Propagation, vector128IncomingValue,
    vector128PreparedValue, vector128InputValues, vector128BinaryValue,
    input_half_low, input_half_high, incoming128Low, incoming128High,
    zip128, lane128_0, lane128_1, pack128_zero, pack128_and, pack128_or,
    UInt256Proof.propagation128, UInt256Proof.zeroDifferenceMask, UInt256Proof.borrowMask,
    CIL.fin_val_three,
    show (4 : Fin 10).val = 4 from rfl,
    show (5 : Fin 10).val = 5 from rfl,
    show (8 : Fin 10).val = 8 from rfl,
    show (9 : Fin 10).val = 9 from rfl,
    show (4 : Fin 8).val = 4 from rfl,
    show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl,
    show (7 : Fin 8).val = 7 from rfl]

  rfl

theorem vector128_no_borrow_propagation (memory : Memory) (left right : Reference)
    (fast : vector128InitialPropagation memory left right = BitVec.ofNat 128 0) :
    UInt256Proof.NoBorrowPropagation (inputLimb memory left) (inputLimb memory right) := by
  rw [vector128_initial_propagation] at fast
  exact UInt256Proof.propagation128_zero _ _ fast

def vector128Corrected (memory : Memory) (left right : Reference) (upper : Bool) : BitVec 128 :=
  let values := vector128IncomingValue (vector128InputValues memory left right)
  zip128 (· + ·) (values (if upper then 5 else 4)) (values (if upper then 9 else 8))

theorem vector128_corrected_words (memory : Memory) (left right : Reference) (upper : Bool) :
    vector128Corrected memory left right upper =
      let words := UInt256Proof.speculativeDifference (inputLimb memory left) (inputLimb memory right)
      pack128 (words (if upper then 2 else 0)) (words (if upper then 3 else 1)) := by
  have correction (x y result : BitVec 64) : result + mask64 (x.ult y) =
      result - UInt256Proof.independentBorrow x y := UInt256Proof.borrow_mask_subtract_raw x y result
  cases upper <;>
    simp [vector128Corrected, vector128IncomingValue, vector128PreparedValue, vector128InputValues,
      vector128BinaryValue, input_half_low, input_half_high, incoming128Low, incoming128High,
      zip128, lane128_0, lane128_1, correction, UInt256Proof.speculativeDifference, CIL.fin_val_three,
      show (4 : Fin 10).val = 4 from rfl, show (5 : Fin 10).val = 5 from rfl,
      show (8 : Fin 10).val = 8 from rfl, show (9 : Fin 10).val = 9 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl]


theorem vector128_corrected_difference (memory : Memory) (left right : Reference) (upper : Bool)
    (fast : vector128InitialPropagation memory left right = BitVec.ofNat 128 0) :
    vector128Corrected memory left right upper =
      pack128 (scalarDifferenceWord memory left right (if upper then 2 else 0))
        (scalarDifferenceWord memory left right (if upper then 3 else 1)) := by
  rw [vector128_corrected_words,
    UInt256Proof.speculative_difference_words _ _ (vector128_no_borrow_propagation memory left right fast),
    ← scalar_difference_words]

def vector128FastFlag (memory : Memory) (left right : Reference) : BitVec 32 :=
  let highMask := vector128IncomingValue (vector128InputValues memory left right) 7
  if BitVec.ofNat 64 0 < lane64 highMask 1 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

theorem vector128_fast_flag (memory : Memory) (left right : Reference)
    (fast : vector128InitialPropagation memory left right = BitVec.ofNat 128 0) :
    vector128FastFlag memory left right = subtractUnderflow memory left right := by
  have mask : lane64 (vector128IncomingValue (vector128InputValues memory left right) 7) 1 =
      UInt256Proof.borrowMask (inputLimb memory left 3) (inputLimb memory right 3) := by
    simp [vector128IncomingValue, vector128PreparedValue, vector128InputValues, vector128BinaryValue,
      input_half_low, input_half_high, zip128, lane128_0, lane128_1,
      show (7 : Fin 10).val = 7 from rfl, UInt256Proof.borrowMask]
    rfl
  have chain := (UInt256Proof.independent_borrow_chain _ _
    (vector128_no_borrow_propagation memory left right fast)).2.2
  change scalarBorrowValue memory left right 4 =
    UInt256Proof.independentBorrow (inputLimb memory left 3) (inputLimb memory right 3) at chain
  dsimp only [vector128FastFlag]
  rw [mask, UInt256Proof.borrow_mask_flag, ← chain]
  change _ = if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0
  rw [← scalar_flag_underflow]
  simp [scalarUnderflowFlag, BitVec.pos_iff_ne_zero]

#print axioms vector128_fast_flag
#print axioms vector128_corrected_words
#print axioms vector128_corrected_difference
#print axioms vector128_initial_propagation
#print axioms vector128_no_borrow_propagation
end UInt256Proof.Subtract.Safety
