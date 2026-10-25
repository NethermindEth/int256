import UInt256.Methods.Equality.NegationSafetyAudit

/-- Reference inequality with checked finite return and caller-memory preservation. -/
theorem UInt256Proof.Equality.scalar_inequality_correctness :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 ≠ values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 :=
  UInt256Proof.Equality.Safety.checked_inequality_binding

#print axioms UInt256Proof.Equality.scalar_inequality_correctness
