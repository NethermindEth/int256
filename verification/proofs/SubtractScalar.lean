import UInt256.Methods.Subtract.SafetyAudit

/-- Production scalar subtraction, including initial operands under valid overlap
    and preservation of caller bytes outside the output. -/
theorem UInt256Proof.Subtract.scalar_correctness :
    UInt256Model.Safety.WrappingBinaryContract (· - ·) Extracted.program Extracted.entryIndex :=
  UInt256Proof.Subtract.Safety.checked_wrapping_binding

#print axioms UInt256Proof.Subtract.scalar_correctness
