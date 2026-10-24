import UInt256.Methods.StorageVector
import UInt256.Methods.Multiply.ProductStorageContract
namespace UInt256Proof.Multiply.ProductStorage
open CIL.Safety UInt256Model.Safety
def vectorBody (profile : CIL.FeatureProfile) := UInt256Proof.StorageVector.template profile true 7

theorem vector_contract (profile : CIL.FeatureProfile) (vector : profile.vector256Accelerated = true)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (vectorBody profile)) : Contract program index :=
  UInt256Proof.StorageVector.store_template_contract profile true 7 vector program index found

#print axioms vector_contract
end UInt256Proof.Multiply.ProductStorage
