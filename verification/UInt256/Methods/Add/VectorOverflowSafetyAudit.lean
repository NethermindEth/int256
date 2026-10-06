import UInt256.Methods.Add.VectorReportingContract

/-- Exact public result-and-overflow contract for the extracted entry. -/
theorem UInt256Proof.Add.Safety.checked_vector_overflow_binding :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat))
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.Add.Safety.checked_vector_reporting_contract

#print axioms UInt256Proof.Add.Safety.checked_vector_overflow_binding
