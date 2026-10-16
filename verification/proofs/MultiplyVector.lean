import Extracted
import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.ProductStorageVector
namespace UInt256Proof.Multiply.Entry
private def vectorContext : Context :=
  ⟨⟨0,1,2,3,4,5,6,0,7⟩, Extracted.profile, Extracted.program,
    rfl, rfl, rfl, rfl, rfl, rfl,
    ProductStorage.vector_contract Extracted.profile rfl Extracted.program 6 rfl⟩
theorem vector_storage_correctness : UInt256Model.Safety.WrappingBinaryContract (· * ·) Extracted.program 0 :=
  scalar_correctness vectorContext rfl rfl rfl rfl rfl
#print axioms vector_storage_correctness
end UInt256Proof.Multiply.Entry
