import UInt256.Methods.Subtract.BorrowHelper
import UInt256.Methods.Subtract.SafetyResult
import UInt256.Methods.Reporting.Arithmetic

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Profile

structure ScalarResult (original final : CIL.Safety.Memory) (values : List Value)
    (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = scalarDifferenceValue original left right
  flag : values = [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

theorem ScalarResult.modular_difference {original final : CIL.Safety.Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    inputValue final output = inputValue original left - inputValue original right :=
  result.value.trans (scalar_difference_value original left right)

#print axioms ScalarResult.modular_difference
end UInt256Proof.Subtract.Safety
