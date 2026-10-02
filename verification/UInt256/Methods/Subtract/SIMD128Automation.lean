import UInt256.Methods.Subtract.SmallAutomation
import UInt256.Arithmetic.SIMDBorrow
import UInt256.VectorRepresentation
import CIL.SIMD.EvaluationLemmas

namespace UInt256Proof

macro "cil_subtract128_execute" facts:term,+ "with" calls:tacticSeq : tactic =>
  `(tactic| cil_subtract_execute CIL.FeatureProfile.evaluate, CIL.Intrinsic.available,
    CIL.evalMemory, CIL.unsafeAsRef, unsafeAdd_byte_nonnegative, CIL.offsetValue, CIL.write128,
    CIL.Vector.zip128, CIL.Vector.pack128_zero, CIL.Vector.lane128_0, CIL.Vector.lane128_1,
    CIL.Vector.adv_incoming, CIL.Vector.sse_incoming_low, CIL.Vector.sse_arm_alignment,
    CIL.Vector.pack128_and, CIL.Vector.pack128_or,
    borrowMask, zeroDifferenceMask, BitVec.ult_eq_decide_lt, $[$facts:term],* with $calls:tacticSeq)

end UInt256Proof
