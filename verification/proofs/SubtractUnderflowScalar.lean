import UInt256.Methods.Subtract.UnderflowSafetyAudit

theorem UInt256Proof.Subtract.underflow_scalar_correctness :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left - right)
      (fun left right => decide (left.toNat < right.toNat))
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.Subtract.Safety.checked_underflow_binding

#print axioms UInt256Proof.Subtract.underflow_scalar_correctness
