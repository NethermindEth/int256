import CIL.SIMD.Incoming128
namespace UInt256Proof.Add.Safety
open CIL.Vector
def halfSum (a b : BitVec 128) : BitVec 128 := zip128 (· + ·) a b
def halfCarry (sum left : BitVec 128) : BitVec 128 := zip128 (fun x y => mask64 (x.ult y)) sum left
def corrected128 (sum incoming : BitVec 128) : BitVec 128 := zip128 (· - ·) sum incoming
def propagating128 (result incoming : BitVec 128) : BitVec 128 := zip128 (fun x y => mask64 (x == y)) result 0 &&& incoming
def selectedPropagation128 (advSimd : Bool) (flag : BitVec 32) (low high : BitVec 128) : BitVec 128 :=
  if advSimd = true ∧ flag = BitVec.ofNat 32 0 then incoming128High low high else low ||| high
end UInt256Proof.Add.Safety
