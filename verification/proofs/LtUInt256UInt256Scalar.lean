import UInt256.Methods.Compare.FamilySafetyAudit

/-- Unsigned ordering of the initial UInt256 values, checked finite return,
    and preservation of caller memory. -/
theorem UInt256Proof.Compare.LtUInt256UInt256.scalar_correctness :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 :=
  UInt256Proof.Compare.Safety.checked_less_binding

#print axioms UInt256Proof.Compare.LtUInt256UInt256.scalar_correctness
