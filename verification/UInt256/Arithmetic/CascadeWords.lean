import UInt256.Arithmetic.RippleMasks
import UInt256.Arithmetic.PackedMasks

open CIL CIL.Vector UInt256Model

namespace UInt256Proof.SIMD

theorem carry_boolean (x y : W64) (incoming : Bool) :
    carry x y (if incoming then 1 else 0) =
      if (x + y).ult x || ((x + y == BitVec.allOnes 64) && incoming) then 1 else 0 := by
  rw [carry_generated_propagated _ _ _ (by cases incoming <;> decide)]
  cases incoming <;>
    simp [Bool.or_eq_true, beq_iff_eq, BitVec.ult_eq_decide_lt]

theorem borrow_boolean (x y : W64) (incoming : Bool) :
    borrow x y (if incoming then 1 else 0) =
      if x.ult y || ((x == y) && incoming) then 1 else 0 := by
  rw [borrow_generated_propagated _ _ _ (by cases incoming <;> decide)]
  cases incoming <;>
    simp [Bool.or_eq_true, beq_iff_eq, BitVec.ult_eq_decide_lt]

def rippleIncoming (generate propagate : Fin 4 → Bool) : Fin 4 → Bool := fun i =>
  if i.val = 0 then false else
  if i.val = 1 then generate 0 else
  if i.val = 2 then generate 1 || (propagate 1 && generate 0) else
    generate 2 || (propagate 2 && (generate 1 || (propagate 1 && generate 0)))

def addGenerate (a b : Limbs) (i : Fin 4) : Bool := (a i + b i).ult (a i)
def addPropagate (a b : Limbs) (i : Fin 4) : Bool := a i + b i == BitVec.allOnes 64
def subtractGenerate (a b : Limbs) (i : Fin 4) : Bool := (a i).ult (b i)
def subtractPropagate (a b : Limbs) (i : Fin 4) : Bool := a i == b i

def addCascadeWords (a b : Limbs) : Limbs := fun i =>
  a i + b i + if rippleIncoming (addGenerate a b) (addPropagate a b) i then 1 else 0

def subtractCascadeWords (a b : Limbs) : Limbs := fun i =>
  a i - b i - if rippleIncoming (subtractGenerate a b) (subtractPropagate a b) i then 1 else 0

theorem add_cascade_words (a b : Limbs) : addCascadeWords a b = sumWords a b := by
  have h0 := carry_boolean (a 0) (b 0) false
  have h1 := carry_boolean (a 1) (b 1) (addGenerate a b 0)
  have h2 := carry_boolean (a 2) (b 2)
    (addGenerate a b 1 || (addPropagate a b 1 && addGenerate a b 0))
  simp only [Bool.false_eq_true, ite_false, Bool.and_false, Bool.or_false] at h0
  simp [addGenerate, addPropagate] at h0 h1 h2
  have chain2 := (congrArg (carry (a 1) (b 1)) h0).trans h1
  have chain3 := (congrArg (carry (a 2) (b 2)) chain2).trans h2
  funext i
  rcases i with ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h
  all_goals subst i
  all_goals simp [addCascadeWords, sumWords, rippleIncoming, addGenerate,
    addPropagate]
  all_goals first | exact h0.symm | exact chain2.symm | exact chain3.symm

theorem subtract_cascade_words (a b : Limbs) :
    subtractCascadeWords a b = differenceWords a b := by
  have h0 := borrow_boolean (a 0) (b 0) false
  have h1 := borrow_boolean (a 1) (b 1) (subtractGenerate a b 0)
  have h2 := borrow_boolean (a 2) (b 2)
    (subtractGenerate a b 1 || (subtractPropagate a b 1 && subtractGenerate a b 0))
  simp only [Bool.false_eq_true, ite_false, Bool.and_false, Bool.or_false] at h0
  simp [subtractGenerate, subtractPropagate] at h0 h1 h2
  have chain2 := (congrArg (borrow (a 1) (b 1)) h0).trans h1
  have chain3 := (congrArg (borrow (a 2) (b 2)) chain2).trans h2
  have h3 : (3 : Fin 4).val = 3 := rfl
  funext i
  rcases i with ⟨i, hi⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h
  all_goals subst i
  all_goals simp [subtractCascadeWords, differenceWords, rippleIncoming, subtractGenerate,
    subtractPropagate, h3]
  all_goals first | exact h0.symm | exact chain2.symm | exact chain3.symm

end UInt256Proof.SIMD
