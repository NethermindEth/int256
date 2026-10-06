import UInt256.Methods.Equality.VectorPrimitiveSafety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem vector_primitive_run64 (memory : Memory) (left : Reference) (right : BitVec 64)
    (frame : Frame) (call : CallingConditions Extracted.program memory [left] []) :
    ∃ fuel, run Extracted.program fuel vectorPrimitiveIndex 0 (scalarArguments left (.i64 right)) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = right.zeroExtend 256 then 1 else 0))]) := by
  have formed := call.input_formed (reference := left) (by simp)
  have loaded := call.input_load (reference := left) (by simp)
  conv in vectorPrimitiveIndex => cbv
  refine ⟨9, ?_⟩
  iterate 8
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, scalarArguments, checkedValue, numericValue, formValue, formed,
            loaded, pureArity, scalars, staticInstruction, memoryInstruction,
            CIL.step, CIL.Intrinsic.available, intrinsic_scalar64, intrinsic_equal256,
            Bitwise.intrinsic_xor256, intrinsic_zero256,
            UInt256Model.Equality.booleanWord, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

  simp only [eq_comm]

theorem vector_primitive_checked64 :
    ReadOnlyScalarContract CIL.Value.i64
      (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
      Extracted.program vectorPrimitiveIndex :=
  certify_readOnly_scalar Extracted.program vectorPrimitiveIndex vectorPrimitiveBody CIL.Value.i64
    (fun left right => .i32 (if left = right.zeroExtend 256 then 1 else 0))
    vector_primitive_found (fun _ => rfl) (fun left right => vector_primitive_fits left (.i64 right))
    vector_primitive_run64

#print axioms vector_primitive_run64
#print axioms vector_primitive_checked64

end UInt256Proof.Equality.Safety
