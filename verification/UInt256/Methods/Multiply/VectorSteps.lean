import UInt256.Methods.Multiply.VectorProducts
import CIL.Safety.Execution
namespace UInt256Proof.Multiply
open CIL.Safety CIL.Vector

theorem step_reverse256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (a b c d : BitVec 64)
    (available : body.profile.avx2 = true) :
    step body (.intrinsic (.avx2 .permute4x64) 2) pc args frame
      (.scalar (.i32 27) :: .scalar (.v256 (pack256 a b c d)) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.v256 (pack256 d c b a)) :: rest) frame memory) := by
  have length : ¬ rest.length + 1 + 1 < 2 := by omega
  simp [length, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    CIL.Intrinsic.available, available, eval_reverse256,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem step_mul256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (a b c d e f g h : BitVec 64)
    (available : CIL.Intrinsic.available body.profile (.avx512DQ .mul64) = true) :
    step body (.intrinsic (.avx512DQ .mul64) 2) pc args frame
      (.scalar (.v256 (pack256 e f g h)) :: .scalar (.v256 (pack256 a b c d)) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.v256 (pack256 (a*e) (b*f) (c*g) (d*h))) :: rest) frame memory) := by
  have length : ¬ rest.length + 1 + 1 < 2 := by omega
  simp [length, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    available, eval_dq_product256, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem step_sum256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (a b c d : BitVec 64) :
    step body (.intrinsic (.vector (.sum64 256)) 1) pc args frame
      (.scalar (.v256 (pack256 a b c d)) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.i64 (a+b+c+d)) :: rest) frame memory) := by
  have lengthOne : ¬ rest.length + 1 < 1 := by omega
  simp [lengthOne, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    CIL.Intrinsic.available, eval_sum256, Bind.bind, Except.bind, Pure.pure, Except.pure]
end UInt256Proof.Multiply
namespace UInt256Proof.Multiply
open CIL.Safety CIL.Vector

theorem step_reinterpret256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (x : BitVec 256) :
    step body (.intrinsic (.vector (.reinterpret 256)) 1) pc args frame
      (.scalar (.v256 x) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.v256 x) :: rest) frame memory) := by
  have length : ¬ rest.length + 1 < 1 := by omega
  simp [length, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    CIL.Intrinsic.available, eval_reinterpret256, Bind.bind, Except.bind, Pure.pure, Except.pure]
theorem step_shift_right256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (a b c d : BitVec 64)
    (available : body.profile.avx2 = true) :
    step body (.intrinsic (.avx2 .shr64) 2) pc args frame
      (.scalar (.i32 32) :: .scalar (.v256 (pack256 a b c d)) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.v256 (pack256 (a >>> 32) (b >>> 32) (c >>> 32) (d >>> 32))) :: rest) frame memory) := by
  have length : ¬ rest.length + 1 + 1 < 2 := by omega
  simp [length, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    CIL.Intrinsic.available, available, eval_shift_right256, Bind.bind, Except.bind, Pure.pure, Except.pure]
theorem step_shift_left256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (a b c d : BitVec 64)
    (available : body.profile.avx2 = true) :
    step body (.intrinsic (.avx2 .shl64) 2) pc args frame
      (.scalar (.i32 32) :: .scalar (.v256 (pack256 a b c d)) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.v256 (pack256 (a <<< 32) (b <<< 32) (c <<< 32) (d <<< 32))) :: rest) frame memory) := by
  have length : ¬ rest.length + 1 + 1 < 2 := by omega
  simp [length, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    CIL.Intrinsic.available, available, eval_shift_left256, Bind.bind, Except.bind, Pure.pure, Except.pure]
theorem step_even_product256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (a b c d e f g h : BitVec 64)
    (available : body.profile.avx2 = true) :
    step body (.intrinsic (.avx2 .multiplyEven32) 2) pc args frame
      (.scalar (.v256 (pack256 e f g h)) :: .scalar (.v256 (pack256 a b c d)) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.v256 (pack256 (digitLow a * digitLow e) (digitLow b * digitLow f) (digitLow c * digitLow g) (digitLow d * digitLow h))) :: rest) frame memory) := by
  have length : ¬ rest.length + 1 + 1 < 2 := by omega
  simp [length, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    CIL.Intrinsic.available, available, eval_even_product256, Bind.bind, Except.bind, Pure.pure, Except.pure]
theorem step_add256 (body : CIL.Method) (pc : Nat) (args rest : List Value)
    (frame : Frame) (memory : Memory) (a b c d e f g h : BitVec 64)
    (available : body.profile.avx2 = true) :
    step body (.intrinsic (.avx2 .add64) 2) pc args frame
      (.scalar (.v256 (pack256 e f g h)) :: .scalar (.v256 (pack256 a b c d)) :: rest) memory =
      .ok (.next (pc+1) (.scalar (.v256 (pack256 (a+e) (b+f) (c+g) (d+h))) :: rest) frame memory) := by
  have length : ¬ rest.length + 1 + 1 < 2 := by omega
  simp [length, step, numericValue, checkedValue, scalars, checkedIntrinsic,
    CIL.Intrinsic.available, available, eval_add256, Bind.bind, Except.bind, Pure.pure, Except.pure]
end UInt256Proof.Multiply