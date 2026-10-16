import UInt256.Methods.Subtract.UnderflowSafety
import UInt256.Methods.Subtract.BorrowCaller

theorem UInt256Proof.Subtract.Safety.checked_underflow_binding :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left - right)
      (fun left right => decide (left.toNat < right.toNat))
      Extracted.program Extracted.entryIndex := by
  with_reducible exact
    (UInt256Proof.Subtract.Safety.checked_underflow_contract UInt256Proof.Subtract.Safety.borrow_checked_contract)

#print axioms UInt256Proof.Subtract.Safety.checked_underflow_binding
