import UInt256.Methods.Compare.ThreeWayLeafContract
import UInt256.Methods.ValueForwarder32

namespace UInt256Proof.Compare.ThreeWayValue
open UInt256Model.Safety

theorem correctness (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (ValueForwarder32.body profile false callee))
    (childFound : program[callee]? = some (ThreeWayLeaf.body profile)) :
    ReadOnlyScalarContract ValueForwarder32.encode
      (fun left right => .i32 (UInt256Model.Compare.compareWord left.toNat right.toNat)) program index :=
  ValueForwarder32.checked profile program index callee false
    (fun left right => UInt256Model.Compare.compareWord left.toNat right.toNat)
    (by intro _ _ impossible; contradiction) found
    (ThreeWayLeaf.threeWay_checked profile program callee childFound)

#print axioms correctness
end UInt256Proof.Compare.ThreeWayValue
