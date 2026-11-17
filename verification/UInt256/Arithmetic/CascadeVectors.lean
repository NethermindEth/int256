import UInt256.Arithmetic.CascadeWords
import CIL.SIMD.Evaluation256Lemmas

open CIL CIL.Vector UInt256Model

namespace UInt256Proof.SIMD

def packedLimbs (a : Limbs) : V256 := pack256 (a 0) (a 1) (a 2) (a 3)
def operationMask (flags : Fin 4 → Bool) : W32 :=
  packedFlags (flags 0) (flags 1) (flags 2) (flags 3)

theorem add_flags_disjoint (a b : Limbs) (i : Fin 4) :
    ¬ (addGenerate a b i && addPropagate a b i) = true := by
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨generated, full⟩ := h
  have hg : a i + b i < a i := by simpa only [addGenerate, BitVec.ult_eq_decide_lt,
    decide_eq_true_eq] using generated
  have hf : a i + b i = BitVec.allOnes 64 := by
    simpa only [addPropagate, beq_iff_eq] using full
  exact carry_not_full _ _ hf hg

theorem subtract_flags_disjoint (a b : Limbs) (i : Fin 4) :
    ¬ (subtractGenerate a b i && subtractPropagate a b i) = true := by
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨generated, equal⟩ := h
  have hg : a i < b i := by simpa only [subtractGenerate, BitVec.ult_eq_decide_lt,
    decide_eq_true_eq] using generated
  have he : a i = b i := by simpa only [subtractPropagate, beq_iff_eq] using equal
  rw [he] at hg
  simp only [BitVec.lt_def] at hg
  omega

theorem ripple_vector (generate propagate : Fin 4 → Bool)
    (disjoint : ∀ i, ¬ (generate i && propagate i) = true) :
    cascadeVector (cascadeIndex (operationMask generate) (operationMask propagate)) =
      packedLimbs (fun i => if rippleIncoming generate propagate i then 1 else 0) := by
  have h := cascade_flags (generate 0) (generate 1) (generate 2) (generate 3)
    (propagate 0) (propagate 1) (propagate 2) (propagate 3)
    (disjoint 0) (disjoint 1) (disjoint 2) (disjoint 3)
  simpa [operationMask, packedLimbs, rippleIncoming,
    show (3 : Fin 4).val = 3 from rfl] using h

theorem add_cascade_vector (a b : Limbs) :
    zip256 (· + ·) (packedLimbs (fun i => a i + b i))
      (cascadeVector (cascadeIndex (operationMask (addGenerate a b))
        (operationMask (addPropagate a b)))) = packedLimbs (sumWords a b) := by
  rw [ripple_vector _ _ (add_flags_disjoint a b), ← add_cascade_words]
  simp only [packedLimbs, zip256, lane256_0, lane256_1, lane256_2, lane256_3,
    addCascadeWords]

theorem subtract_cascade_vector (a b : Limbs) :
    zip256 (· - ·) (packedLimbs (fun i => a i - b i))
      (cascadeVector (cascadeIndex (operationMask (subtractGenerate a b))
        (operationMask (subtractPropagate a b)))) = packedLimbs (differenceWords a b) := by
  rw [ripple_vector _ _ (subtract_flags_disjoint a b), ← subtract_cascade_words]
  simp only [packedLimbs, zip256, lane256_0, lane256_1, lane256_2, lane256_3,
    subtractCascadeWords]

end UInt256Proof.SIMD
