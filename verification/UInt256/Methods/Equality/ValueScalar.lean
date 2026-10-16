import UInt256.Methods.Equality.ReferenceScalar
import UInt256.Methods.ValueForwarder32

namespace UInt256Proof.Equality.ValueScalar
open UInt256Model.Safety

abbrev body (profile : CIL.FeatureProfile) (callee : Nat) := ValueForwarder32.body profile true callee
abbrev encode := ValueForwarder32.encode

/-- The by-value argument is copied into a private home and compared with the initial receiver. -/
theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee leaf : Nat)
    (vector : profile.vector256Accelerated = false) (sse : profile.sse41 = false)
    (found : program[index]? = some (body profile callee))
    (childFound : program[callee]? = some (ReferenceScalar.body profile leaf))
    (leafFound : program[leaf]? = some (ScalarLeaf.body profile)) :
    ReadOnlyScalarContract encode (fun left right => .i32 (if left = right then 1 else 0)) program index :=
  ValueForwarder32.checked profile program index callee true
    (fun left right => if left = right then 1 else 0)
    (by intro left right _; split <;> simp) found
    (ReferenceScalar.checked profile program callee leaf vector sse childFound leafFound)

#print axioms checked
end UInt256Proof.Equality.ValueScalar
