import UInt256.Methods.Add.OverflowSafetyAudit

/-- Addition modulo 2^256, exact unsigned carry, checked finite return and
    caller-memory preservation under valid operand/output overlap. -/
theorem UInt256Proof.Add.overflow_scalar_correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat))
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.Safety.checked_overflow_binding

#print axioms UInt256Proof.Add.overflow_scalar_correctness
