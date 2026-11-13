import CIL.SIMD.Evaluation256Lemmas
namespace UInt256Proof.Add.Safety
def generatedCarry (a b : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun sum left => CIL.Vector.mask64 (sum.ult left))
    (CIL.Vector.zip256 (· + ·) a b) a

def incomingCarry (mask : BitVec 256) : BitVec 256 :=
  CIL.Vector.blend32 (CIL.Vector.permute4x64 mask (BitVec.ofNat 8 144))
    (BitVec.ofNat 256 0) (BitVec.ofNat 8 3)

theorem incomingCarry_packed (a b c d : BitVec 64) :
    incomingCarry (CIL.Vector.pack256 a b c d) = CIL.Vector.pack256 0 a b c := by
  change CIL.Vector.blend32 (CIL.Vector.permute4x64 (CIL.Vector.pack256 a b c d) 144) 0 3 = _
  rw [CIL.Vector.avx2_permute_incoming, CIL.Vector.avx2_blend_incoming]

def propagationMask (sum : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) sum (~~~(BitVec.ofNat 256 0))


end UInt256Proof.Add.Safety
