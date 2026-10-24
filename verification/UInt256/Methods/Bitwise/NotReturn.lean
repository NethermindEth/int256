import UInt256.Methods.Bitwise.ReturnComposition
import UInt256.Methods.Bitwise.NotScalar

namespace UInt256Proof.Bitwise.ReturnSafety

theorem unary_correctness (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (program : CIL.Program)
    (index callee constructor : Nat)
    (found : program[index]? = some (unaryBody profile callee))
    (childFound : program[callee]? = some (notBody profile constructor))
    (constructorFound : program[constructor]? = some (UInt256Proof.ConstructorSafety.body profile)) :
    UnaryContract (~~~·) program index :=
  unary_checked (~~~·) profile program index callee found
    (not_result profile scalar program callee constructor childFound constructorFound)

#print axioms unary_correctness
end UInt256Proof.Bitwise.ReturnSafety
