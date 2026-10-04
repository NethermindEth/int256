import UInt256.Methods.Multiply.SingleDispatch
import UInt256.Methods.Multiply.SmallExecution
import UInt256.Methods.Multiply.MultiLimbExecution
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

def multiplyOutput (memory : Memory) (out : Nat) (a b : Limbs) : Memory :=
  writeBytes memory out (value a * value b).toNat 32

theorem execute_entry (memory : Memory) (left right out frame fuel : Nat) (a b : Limbs)
    (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) = some (.i64 (a i)))
    (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) = some (.i64 (b i))) :
    ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
        Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
      ∀ address, final (.byte address) = multiplyOutput memory out a b (.byte address) := by
  multiply_without_recovery
    by_cases leftSmall : a 1 ||| (a 2 ||| a 3) = BitVec.ofNat 64 0
    · have leftShape := singleWord_eq a leftSmall
      by_cases rightSmall : b 1 ||| (b 2 ||| b 3) = BitVec.ofNat 64 0
      · have rightShape := singleWord_eq b rightSmall
        have smallLeftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) =
            some (.i64 (if i = 0 then a 0 else 0)) := by
          intro i
          have reads := leftReads i
          rw [← congrFun leftShape i] at reads
          exact reads
        have smallRightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) =
            some (.i64 (if i = 0 then b 0 else 0)) := by
          intro i
          have reads := rightReads i
          rw [← congrFun rightShape i] at reads
          exact reads
        have caseResult : ∃ final,
          run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
            Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
          ∀ address, final (.byte address) = store4 memory out (lowProduct (a 0) (b 0)) (highProduct (a 0) (b 0)) 0 0 (.byte address) := by
          first
          | multiply_checked_case UInt256Proof.Multiply.execute_single_words (memory,left,right,out,frame,fuel,a 0,b 0,smallLeftReads,smallRightReads)
          | multiply_single_word_case memory,left,right,(a 0),(b 0),smallLeftReads,smallRightReads
        obtain ⟨final, execution, bytes⟩ := caseResult
        refine ⟨final, execution, ?_⟩
        intro address
        rw [bytes, store4_value]
        change writeBytes memory out
          (value (fun i => if i = 0 then lowProduct (a 0) (b 0) else
            if i = 1 then highProduct (a 0) (b 0) else BitVec.ofNat 64 0)).toNat 32 (.byte address) = _
        rw [single_product_value, leftShape, rightShape]
        rfl
      · have caseResult : ∃ final,
          run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
            Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
          ∀ address, final (.byte address) = store4 memory out (scalarLimbs b (a 0) 0) (scalarLimbs b (a 0) 1) (scalarLimbs b (a 0) 2) (scalarLimbs b (a 0) 3) (.byte address) := by
          first
          | multiply_checked_case UInt256Proof.Multiply.execute_left_word_dispatch (memory,left,right,out,frame,fuel,a,b,leftSmall,rightSmall,leftReads,rightReads)
          | multiply_word_dispatch_case memory,left,right,a,b,leftReads,rightReads,leftSmall,rightSmall
        obtain ⟨final, execution, bytes⟩ := caseResult
        refine ⟨final, execution, ?_⟩
        intro address
        rw [bytes, store4_value]
        change writeBytes memory out (value (scalarLimbs b (a 0))).toNat 32 (.byte address) = _
        rw [scalar_limbs_correct, ← singleWord_value, leftShape, BitVec.mul_comm]
        rfl
    · by_cases rightSmall : b 1 ||| (b 2 ||| b 3) = BitVec.ofNat 64 0
      · have rightShape := singleWord_eq b rightSmall
        have caseResult : ∃ final,
          run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
            Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
          ∀ address, final (.byte address) = store4 memory out (scalarLimbs a (b 0) 0) (scalarLimbs a (b 0) 1) (scalarLimbs a (b 0) 2) (scalarLimbs a (b 0) 3) (.byte address) := by
          first
          | multiply_checked_case UInt256Proof.Multiply.execute_right_word_dispatch (memory,left,right,out,frame,fuel,a,b,leftSmall,rightSmall,leftReads,rightReads)
          | multiply_word_dispatch_case memory,left,right,a,b,leftReads,rightReads,leftSmall,rightSmall
        obtain ⟨final, execution, bytes⟩ := caseResult
        refine ⟨final, execution, ?_⟩
        intro address
        rw [bytes, store4_value]
        change writeBytes memory out (value (scalarLimbs a (b 0))).toNat 32 (.byte address) = _
        rw [scalar_limbs_correct, ← singleWord_value, rightShape]
        rfl
      · have caseResult : ∃ final,
          run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
            Extracted.entryIndex 0 [.object left, .object right, .object out] frame [] memory = some (final, []) ∧
          ∀ address, final (.byte address) = store4 memory out (productLimbs a b 0) (productLimbs a b 1) (productLimbs a b 2) (productLimbs a b 3) (.byte address) := by
          first
          | multiply_checked_case UInt256Proof.Multiply.execute_multi_limb_dispatch (memory,left,right,out,frame,fuel,a,b,leftSmall,rightSmall,leftReads,rightReads)
          | multiply_multi_limb_case memory,left,right,a,b,leftReads,rightReads,leftSmall,rightSmall
        obtain ⟨final, execution, bytes⟩ := caseResult
        refine ⟨final, execution, ?_⟩
        intro address
        rw [bytes, store4_value]
        change writeBytes memory out (value (productLimbs a b)).toNat 32 (.byte address) = _
        rw [product_limbs_correct]
        rfl
end UInt256Proof.Multiply
#print axioms UInt256Proof.Multiply.execute_entry
