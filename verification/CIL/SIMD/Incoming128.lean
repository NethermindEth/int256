import CIL.SIMD.EvaluationLemmas

namespace CIL.Vector

def incoming128Low (low : BitVec 128) : BitVec 128 :=
  CIL.Vector.pack128 0 (CIL.Vector.lane64 low 0)

def incoming128High (low high : BitVec 128) : BitVec 128 :=
  CIL.Vector.pack128 (CIL.Vector.lane64 low 1) (CIL.Vector.lane64 high 0)

theorem incoming128_arm_low (low : BitVec 128) :
    CIL.Vector.advExtract64 (BitVec.ofNat 128 0) low 1 = incoming128Low low := by
  simpa only [CIL.Vector.pack128_lanes, incoming128Low] using
    CIL.Vector.adv_incoming_zero (CIL.Vector.lane64 low 0) (CIL.Vector.lane64 low 1)

theorem incoming128_arm_high (low high : BitVec 128) :
    CIL.Vector.advExtract64 low high 1 = incoming128High low high := by
  simpa only [CIL.Vector.pack128_lanes, incoming128High] using CIL.Vector.adv_incoming
    (CIL.Vector.lane64 low 0) (CIL.Vector.lane64 low 1)
    (CIL.Vector.lane64 high 0) (CIL.Vector.lane64 high 1)

theorem incoming128_sse_low (low : BitVec 128) :
    CIL.Vector.sseShiftLeftBytes low 8 = incoming128Low low := by
  simpa only [CIL.Vector.pack128_lanes, incoming128Low] using
    CIL.Vector.sse_incoming_low (CIL.Vector.lane64 low 0) (CIL.Vector.lane64 low 1)

theorem incoming128_sse_high (low high : BitVec 128) :
    CIL.Vector.ssseAlignBytes high low 8 = incoming128High low high := by
  change CIL.Vector.advExtract64 low high 1 = _
  exact incoming128_arm_high low high


end CIL.Vector
