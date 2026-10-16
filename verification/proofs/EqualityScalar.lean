import UInt256.Methods.Equality.SafetyAudit

/-- Reference equality on the initial UInt256 values, with checked finite return
    and preservation of caller memory. -/
theorem UInt256Proof.Equality.scalar_correctness :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if values[0]?.getD 0 = values[1]?.getD 0 then 1 else 0))
      Extracted.program Extracted.entryIndex 2 :=
  UInt256Proof.Equality.Safety.checked_equality_binding

#print axioms UInt256Proof.Equality.scalar_correctness
