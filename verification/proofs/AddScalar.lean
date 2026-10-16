import UInt256.Methods.Add.EntrySafety
import UInt256.Methods.Add.CarryResult

/-- Scalar production Add: wrapping arithmetic on the initial operands, checked
    finite execution, writable output, and preservation outside its footprint. -/
theorem UInt256Proof.Add.scalar_correctness :
    UInt256Model.Safety.WrappingBinaryContract (· + ·) Extracted.program Extracted.entryIndex :=
  UInt256Proof.Safety.checked_add_contract UInt256Proof.Safety.carry_checked_contract

#print axioms UInt256Proof.Add.scalar_correctness
