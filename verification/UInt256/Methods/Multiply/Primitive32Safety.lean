import UInt256.Methods.Multiply.PrimitiveSafetyContract
import UInt256.Methods.Multiply.WordConversionSafety
import UInt256.Safety.OrderedScalarContract

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem conversion_prefix32 (word : BitVec 32) : ConversionPrefix (.i32 word) (word.setWidth 64) := by
  intro memory frame post continuation
  have found : Extracted.program[conversionIndex]? = some conversionBody := by rfl
  iterate 8
    apply run_next_exists post found (by rfl)
    simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation

theorem uint32_conversion_invoke (memory : Memory) (word : BitVec 32)
    (call : CallingConditions Extracted.program memory [] []) :
    ∃ fuel final,
      invoke Extracted.program fuel conversionIndex [.scalar (.i32 word)] memory =
        .ok (final, [.scalar (.v256 (BitVec.ofNat 256 word.toNat))]) ∧
      final.WellFormed ∧ AccessBelow memory.nextIdentity memory final ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  simpa only [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using
    conversion_invoke memory (.i32 word) (word.setWidth 64) rfl (conversion_prefix32 word) call

#print axioms conversion_prefix32
#print axioms uint32_conversion_invoke

theorem multiply_primitive32_contract (word : WordContract) (top : FullTopContract) :
    OrderedScalarContract primitiveScalarFirst CIL.Value.i32
      (fun input scalar => .v256 (input * BitVec.ofNat 256 scalar.toNat))
      Extracted.program Extracted.entryIndex := by
  intro memory input scalar call
  simpa only [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using
    primitive_checked word top primitiveScalarFirst memory input (.i32 scalar) (scalar.setWidth 64)
      rfl (conversion_prefix32 scalar) (by rfl) (by rfl) (by rfl) call

#print axioms multiply_primitive32_contract
end UInt256Proof.Multiply.Safety
