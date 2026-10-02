import CIL.Features
import CIL.SIMD.Intrinsics

namespace CIL

-- Portable Vector128/Vector256 operations have executable software semantics.
-- ISA-specific operations additionally require their runtime-visible capability.
def Intrinsic.available (profile : FeatureProfile) : Intrinsic → Bool
  | .vector _ => true
  | .advSimd _ => profile.advSimd
  | .sse .shiftLeftBytes => profile.sse2
  | .sse .alignBytes => profile.ssse3
  | .avx _ => profile.avx
  | .avx2 _ => profile.avx2
  | .avx512 _ => profile.avx512F && profile.avx512FVL
  | .bmi1 _ => profile.bmi1

end CIL
