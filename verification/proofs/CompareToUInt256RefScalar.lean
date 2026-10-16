import UInt256.Methods.Compare.ThreeWaySafetyAudit

theorem UInt256Proof.Compare.CompareToUInt256Ref.scalar_correctness :
    UInt256Model.Safety.ReadOnlyContract
      (fun values => .i32 (UInt256Model.Compare.compareWord
        (values[0]?.getD 0).toNat (values[1]?.getD 0).toNat))
      Extracted.program Extracted.entryIndex 2 :=
  UInt256Proof.Compare.Safety.checked_threeWay_binding

#print axioms UInt256Proof.Compare.CompareToUInt256Ref.scalar_correctness
