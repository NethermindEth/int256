import UInt256.Arithmetic.SIMDCarry
import UInt256.VectorRepresentation
import CIL.SIMD.EvaluationLemmas
open CIL CIL.Vector UInt256Model
namespace UInt256Proof.SIMD
def correctedLo (a b : Limbs) : V128 :=
  pack128 (a 0 + b 0) (a 1 + b 1 - carryMask (a 0) (b 0))
def correctedHi (a b : Limbs) : V128 :=
  pack128 (a 2 + b 2 - carryMask (a 1) (b 1))
    (a 3 + b 3 - carryMask (a 2) (b 2))
def propagationLo (a b : Limbs) : V128 :=
  zip128 (fun x y => mask64 (x == y)) (correctedLo a b) (BitVec.ofNat 128 0) &&&
    pack128 (BitVec.ofNat 64 0) (carryMask (a 0) (b 0))
def propagationHi (a b : Limbs) : V128 :=
  zip128 (fun x y => mask64 (x == y)) (correctedHi a b) (BitVec.ofNat 128 0) &&&
    pack128 (carryMask (a 1) (b 1)) (carryMask (a 2) (b 2))
def propagationARM (a b : Limbs) : V128 :=
  advExtract64 (propagationLo a b) (propagationHi a b) 1

def extraHi (a b : Limbs) : V128 :=
  propagationARM a b ||| advExtract64 (BitVec.ofNat 128 0)
    (zip128 (fun x y => mask64 (x == y)) (correctedHi a b)
      (~~~(BitVec.ofNat 128 0)) &&& propagationARM a b) 1

def repairedHi (a b : Limbs) : V128 := zip128 (· - ·) (correctedHi a b) (extraHi a b)

def armStores (m : Memory) (out : Nat) (a b : Limbs) : Memory :=
  let early := writeBytes (writeBytes m out (correctedLo a b).toNat 16)
    (out + 16) (correctedHi a b).toNat 16
  if propagationARM a b = BitVec.ofNat 128 0 then early else
    writeBytes early (out + 16) (repairedHi a b).toNat 16

@[simp] theorem intrinsic_ones128 :
    evalIntrinsic (.vector (.ones 128)) [] = some (.v128 (~~~0)) := rfl

@[simp] theorem pack128_complement (a b : W64) :
    ~~~(pack128 a b) = pack128 (~~~a) (~~~b) := BitVec.not_append


end UInt256Proof.SIMD
