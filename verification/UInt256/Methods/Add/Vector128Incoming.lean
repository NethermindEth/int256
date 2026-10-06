import UInt256.Methods.Add.Vector128Start
import UInt256.Methods.AddSubtract.Vector128Incoming

namespace UInt256Proof.Add.Safety

@[simp] theorem incoming128Offset_add : UInt256Proof.AddSubtract.Safety.incoming128Offset = 0 := by rfl

export CIL.Vector (incoming128Low incoming128High incoming128_arm_low incoming128_arm_high
  incoming128_sse_low incoming128_sse_high)
end UInt256Proof.Add.Safety
