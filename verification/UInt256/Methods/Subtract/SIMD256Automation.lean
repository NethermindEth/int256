import UInt256.Methods.Subtract.SIMD128Automation
import CIL.SIMD.Evaluation256Lemmas
import UInt256.Arithmetic.CascadeWords
import UInt256.Arithmetic.PackedMasks
import UInt256.Arithmetic.SignMasks
import UInt256.Arithmetic.CascadeVectors
import UInt256.LookupAutomation

namespace UInt256Proof

macro "cil_subtract256_execute" facts:term,+ "with" calls:tacticSeq : tactic =>
  `(tactic| cil_subtract_execute CIL.FeatureProfile.evaluate, CIL.Intrinsic.available,
    CIL.evalMemory, CIL.unsafeAsRef, CIL.offsetValue, CIL.write256,
    CIL.Vector.zip256,
    CIL.Vector.lane256_0, CIL.Vector.lane256_1,
    CIL.Vector.lane256_2, CIL.Vector.lane256_3,
    CIL.Vector.pack256_and, CIL.Vector.pack256_or, CIL.Vector.pack256_not,
    CIL.Vector.avx2_permute_incoming, CIL.Vector.avx512_incoming,
    CIL.Vector.avx2_incoming_mask,
    CIL.Vector.avx2_incoming_blend_normal,
    CIL.Vector.avx512_incoming_normal,
    UInt256Proof.SIMD.ternary_borrow_packed_normal,
    CIL.Vector.bextr_flag_bound,
    UInt256Proof.byte_cast_bound,
    CIL.Vector.pack256_zero, borrowMask, BitVec.ult_eq_decide_lt,
    $[$facts:term],* with $calls:tacticSeq)

end UInt256Proof
