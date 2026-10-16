import UInt256.Methods.Bitwise.ReturnComposition
import UInt256.Methods.Bitwise.ScalarSafetyContract

namespace UInt256Proof.Bitwise.ReturnSafety
open UInt256Model.Bitwise

theorem binary_correctness (operation : Binary) (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (program : CIL.Program)
    (index callee constructor : Nat)
    (found : program[index]? = some (binaryBody profile callee))
    (childFound : program[callee]? = some (scalarBody profile operation constructor))
    (constructorFound : program[constructor]? = some (UInt256Proof.ConstructorSafety.body profile)) :
    BinaryContract (applyBinary operation) program index :=
  binary_checked (applyBinary operation) profile program index callee found
    (scalar_result operation profile scalar program callee constructor childFound constructorFound)

#print axioms binary_correctness
end UInt256Proof.Bitwise.ReturnSafety
