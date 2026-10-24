import UInt256.Methods.Bitwise.ReturnComposition
import UInt256.Methods.Bitwise.VectorSafety
import UInt256.Methods.Bitwise.NotVectorSafety

namespace UInt256Proof.Bitwise.VectorReturn
open UInt256Model.Bitwise UInt256Proof.Bitwise.ReturnSafety

theorem binary_correctness (operation : Binary) (profile : CIL.FeatureProfile)
    (enabled : profile.vector256Accelerated = true) (program : CIL.Program)
    (index callee leaf : Nat)
    (found : program[index]? = some (binaryBody profile callee))
    (childFound : program[callee]? = some (VectorSafety.entryBody profile leaf))
    (leafFound : program[leaf]? = some (VectorSafety.body profile operation)) :
    BinaryContract (applyBinary operation) program index := by
  apply binary_checked (applyBinary operation) profile program index callee found
  intro memory left right output call
  obtain ⟨fuel, final, certificate, loaded, writable, outside⟩ :=
    VectorSafety.entry_result profile enabled operation program callee leaf childFound leafFound memory left right output call
  exact ⟨fuel, final, certificate, loaded, writable, fun id _ offset away => outside id offset away⟩

theorem unary_correctness (profile : CIL.FeatureProfile)
    (enabled : profile.vector256Accelerated = true) (program : CIL.Program)
    (index callee leaf : Nat)
    (found : program[index]? = some (unaryBody profile callee))
    (childFound : program[callee]? = some (NotVectorSafety.entryBody profile leaf))
    (leafFound : program[leaf]? = some (NotVectorSafety.body profile)) :
    UnaryContract (~~~·) program index := by
  apply unary_checked (~~~·) profile program index callee found
  intro memory input output call
  obtain ⟨fuel, final, certificate, loaded, writable, outside⟩ :=
    NotVectorSafety.entry_result profile enabled program callee leaf childFound leafFound memory input output call
  exact ⟨fuel, final, certificate, loaded, writable, fun id _ offset away => outside id offset away⟩

#print axioms binary_correctness
#print axioms unary_correctness
end UInt256Proof.Bitwise.VectorReturn
