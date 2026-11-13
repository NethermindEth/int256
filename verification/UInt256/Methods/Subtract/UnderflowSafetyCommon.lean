import UInt256.Methods.Subtract.Bindings
import UInt256.Safety.ReportingForwarder

/-! The extracted public SubtractUnderflow entry forwards its three references to SubtractImpl
    and returns its byte flag. -/

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

/-- Public SubtractUnderflow keeps the forwarded underflow flag, difference and footprint. -/
theorem underflow_contract_of_reporting
    (reporting : ReportingBinaryContract (· - ·)
      (fun a b => decide (a.toNat < b.toNat)) Extracted.program Extracted.subtractVector256Index) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat))
      Extracted.program Extracted.entryIndex :=
  forward_reporting_byte Extracted.program Extracted.entryIndex Extracted.subtractVector256Index
    Extracted.entryBody _ _ rfl rfl rfl rfl rfl rfl rfl reporting

end UInt256Proof.Subtract.Safety
