import CIL.Memory

open CIL

namespace UInt256Model

abbrev Limbs := Fin 4 → W64

def value (a : Limbs) : BitVec 256 :=
  BitVec.ofNat 256 ((a 0).toNat + (a 1).toNat * 2^64 +
    (a 2).toNat * 2^128 + (a 3).toNat * 2^192)

def decode (v : BitVec 256) : Limbs := fun i =>
  BitVec.ofNat 64 (v.toNat / 2 ^ (64 * i.val))
abbrev Bytes := Nat → BitVec 8

def byteMemory (m : Bytes) : Memory
  | .byte address => some (.i8 (m address))
  | _ => none

def byteNumber (m : Bytes) (base : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (m base).toNat + 256 * byteNumber m (base + 1) n

def byteValue (m : Bytes) (base : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (byteNumber m base 32)

end UInt256Model
