import UInt256.Methods.Compare.ThreeWayLeaf
import UInt256.Methods.Compare.Lemmas
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Compare.ThreeWayLeaf
open CIL.Safety UInt256Model.Safety

theorem threeWay_input_value (memory : Memory) (reference : Reference) :
    UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
  UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

theorem threeWay_result_math (memory : Memory) (left right : Reference) :
    threeWayResult memory left right = UInt256Model.Compare.compareWord
      (inputValue memory left).toNat (inputValue memory right).toNat := by
  have order := UInt256Proof.Compare.value_lt_descending (inputLimb memory left) (inputLimb memory right)
  have equal := UInt256Proof.Equality.value_eq_iff (inputLimb memory left) (inputLimb memory right)
  rw [threeWay_input_value, threeWay_input_value] at order equal
  simp only [UInt256Model.Compare.compareWord, BitVec.toNat_inj, equal, order]
  by_cases h3 : inputLimb memory left 3 = inputLimb memory right 3 <;>
    by_cases h2 : inputLimb memory left 2 = inputLimb memory right 2 <;>
    by_cases h1 : inputLimb memory left 1 = inputLimb memory right 1 <;>
    by_cases h0 : inputLimb memory left 0 = inputLimb memory right 0 <;>
    simp [threeWayResult, h3, h2, h1, h0, BitVec.lt_def]


theorem threeWay_checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile)) (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (UInt256Model.Compare.compareWord
          (inputValue memory left).toNat (inputValue memory right).toNat))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  apply certify_readOnly_binary program index (body profile)
    (fun left right => .i32 (UInt256Model.Compare.compareWord left.toNat right.toNat))
    found ?_ ?_ memory left right call
  · intro left right
    simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit]
  · intro memory left right frame call
    simpa only [threeWay_result_math] using threeWay_run profile program index found memory left right frame call

#print axioms threeWay_checked

#print axioms threeWay_result_math
end UInt256Proof.Compare.ThreeWayLeaf
