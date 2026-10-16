import UInt256.Methods.Equality.PrimitiveChecked
import UInt256.Safety.ScalarOperatorContract

namespace UInt256Proof.Equality.UnsignedPrimitive
open CIL.Safety UInt256Model.Safety PrimitiveFinish

def body64 (profile : CIL.FeatureProfile) (scalarIndex constructorIndex : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 15,
  .arg 0,
  .arg 1,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .newAggregate constructorIndex 4 32,
  .setLocal 0,
  .localAddr 0,
  .call scalarIndex 2,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

def body32 (profile : CIL.FeatureProfile) (scalarIndex constructorIndex : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.aggregate (List.replicate 32 0)], localKinds := [.aggregate 32], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 16,
  .arg 0,
  .arg 1,
  .convU8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .newAggregate constructorIndex 4 32,
  .setLocal 0,
  .localAddr 0,
  .call scalarIndex 2,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

macro "primitive_prefix" found:term "," inactive:term : tactic => `(tactic|
  (intro memory left frame call post continuation
   have formed := call.input_formed (reference := left) (by simp)
   simp only [constructorWords, List.reverse_cons, List.reverse_nil,
     List.nil_append, List.cons_append] at continuation
   repeat' first
     | exact continuation
     | (apply run_next_exists post $found
        · simp only [body32, body64]; rfl
        · simp [body32, body64, step, primitiveArguments, checkedValue, numericValue, formValue, formed,
            pureArity, scalars, instruction, CIL.unary, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate, $inactive:term,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (exact ⟨rfl, rfl, rfl, rfl⟩))))

theorem prefix64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body64 profile scalarIndex constructorIndex)) (right : BitVec 64) :
    PrimitivePrefix program index 10 (.i64 right) right := by
  primitive_prefix found, inactive

#print axioms prefix64

theorem prefix32 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body32 profile scalarIndex constructorIndex)) (right : BitVec 32) :
    PrimitivePrefix program index 11 (.i32 right) (BitVec.zeroExtend 64 right) := by
  primitive_prefix found, inactive

#print axioms prefix32

theorem checked64 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body64 profile scalarIndex constructorIndex))
    (scalarFound : program[scalarIndex]? = some (ScalarLeaf.body profile))
    (constructorFound : program[constructorIndex]? = some (ConstructorSafety.body profile)) :
    ScalarOperatorContract false false CIL.Value.i64
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  intro memory left right call
  simpa only [scalarOperatorArguments, Bool.false_eq_true, ite_false, scalarArguments, primitiveArguments,
    Bool.bne_false, decide_eq_true_eq] using
    primitive_checked program index 10 scalarIndex constructorIndex (body64 profile scalarIndex constructorIndex) profile
      found rfl rfl rfl rfl rfl rfl scalarFound constructorFound rfl rfl rfl rfl memory left (.i64 right) right
      rfl (prefix64 profile program index scalarIndex constructorIndex inactive found right) call

#print axioms checked64

set_option maxHeartbeats 800000 in
theorem checked32 (profile : CIL.FeatureProfile) (program : CIL.Program) (index scalarIndex constructorIndex : Nat)
    (inactive : profile.vector256Accelerated = false)
    (found : program[index]? = some (body32 profile scalarIndex constructorIndex))
    (scalarFound : program[scalarIndex]? = some (ScalarLeaf.body profile))
    (constructorFound : program[constructorIndex]? = some (ConstructorSafety.body profile)) :
    ScalarOperatorContract false false CIL.Value.i32
      (fun input word => decide (input = BitVec.ofNat 256 word.toNat)) program index := by
  intro memory left right call
  have widen : (BitVec.zeroExtend 64 right).toNat = right.toNat :=
    BitVec.toNat_setWidth_of_le (by decide)
  simpa only [scalarOperatorArguments, Bool.false_eq_true, ite_false, scalarArguments, primitiveArguments,
    Bool.bne_false, decide_eq_true_eq, widen] using
    primitive_checked program index 11 scalarIndex constructorIndex (body32 profile scalarIndex constructorIndex) profile
      found rfl rfl rfl rfl rfl rfl scalarFound constructorFound rfl rfl rfl rfl memory left (.i32 right) (BitVec.zeroExtend 64 right)
      rfl (prefix32 profile program index scalarIndex constructorIndex inactive found right) call

#print axioms checked32
end UInt256Proof.Equality.UnsignedPrimitive
