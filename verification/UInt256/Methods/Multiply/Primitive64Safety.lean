import UInt256.Methods.Multiply.PrimitiveSafetyContract
import UInt256.Methods.Multiply.WordConversionSafety
import UInt256.Safety.OrderedScalarContract

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem conversion_prefix64 (word : BitVec 64) : ConversionPrefix (.i64 word) word := by
  intro memory frame post continuation
  have found : Extracted.program[conversionIndex]? = some conversionBody := by rfl
  iterate 7
    apply run_next_exists post found (by rfl)
    simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation

theorem word_conversion_invoke (memory : Memory) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [] []) :
    ∃ fuel final,
      invoke Extracted.program fuel conversionIndex [.scalar (.i64 word)] memory =
        .ok (final, [.scalar (.v256 (BitVec.ofNat 256 word.toNat))]) ∧
      final.WellFormed ∧ AccessBelow memory.nextIdentity memory final ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  conversion_invoke memory (.i64 word) word rfl (conversion_prefix64 word) call

#print axioms conversion_prefix64
#print axioms word_conversion_invoke

theorem multiply_primitive64_contract (word : WordContract) (top : FullTopContract) :
    OrderedScalarContract primitiveScalarFirst CIL.Value.i64
      (fun input scalar => .v256 (input * BitVec.ofNat 256 scalar.toNat))
      Extracted.program Extracted.entryIndex := by
  intro memory input scalar call
  exact primitive_checked word top primitiveScalarFirst memory input (.i64 scalar) scalar
    rfl (conversion_prefix64 scalar) (by rfl) (by rfl) (by rfl) call

#print axioms multiply_primitive64_contract
end UInt256Proof.Multiply.Safety
