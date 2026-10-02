import CIL.Types

namespace CIL.Vector

abbrev V128 := BitVec 128
abbrev V256 := BitVec 256

/-- Lane zero occupies the least significant bits, matching little-endian byte memory. -/
def lane64 (x : BitVec n) (i : Nat) : W64 := x.extractLsb' (64 * i) 64
def lane32 (x : BitVec n) (i : Nat) : W32 := x.extractLsb' (32 * i) 32
def pack128 (a0 a1 : W64) : V128 := a1 ++ a0
def pack256 (a0 a1 a2 a3 : W64) : V256 := (a3 ++ a2) ++ (a1 ++ a0)

def map128 (f : W64 → W64) (x : V128) : V128 :=
  pack128 (f (lane64 x 0)) (f (lane64 x 1))
def map256 (f : W64 → W64) (x : V256) : V256 :=
  pack256 (f (lane64 x 0)) (f (lane64 x 1)) (f (lane64 x 2)) (f (lane64 x 3))
def zip128 (f : W64 → W64 → W64) (x y : V128) : V128 :=
  pack128 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
def zip256 (f : W64 → W64 → W64) (x y : V256) : V256 :=
  pack256 (f (lane64 x 0) (lane64 y 0)) (f (lane64 x 1) (lane64 y 1))
    (f (lane64 x 2) (lane64 y 2)) (f (lane64 x 3) (lane64 y 3))

def mask64 (p : Bool) : W64 := if p then ~~~(0 : W64) else 0
def reinterpret (x : BitVec n) : BitVec n := x

end CIL.Vector
