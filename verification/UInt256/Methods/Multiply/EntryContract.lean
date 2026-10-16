import UInt256.Methods.Multiply.EntryDispatch
import UInt256.Safety.AggregateReturn
import UInt256.Safety.ArgumentValues

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

theorem multiply_checked_result (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word)
    (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage)
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions ctx.program memory [left, right] [output]) :
    ∃ fuel final,
      InvocationCertificate ctx.program ctx.indices.entry (binaryArguments left right output) memory fuel final [] ∧
      OutputResult memory final output (inputValue memory left * inputValue memory right) [] := by
  obtain ⟨fuel, final, invoked, result⟩ := multiply_invoke ctx word top memory left right output call
  obtain ⟨frame, entered, setup, _, _, _⟩ := multiply_frame_setup ctx memory left right output call
  have found := ctx.entry
  have fl := call.input_formed (by simp : left ∈ [left, right])
  have fr := call.input_formed (by simp : right ∈ [left, right])
  have fo := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) =
      .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, checkedAt, fl, fr, fo,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := call.binary_entry_live setup
  have ran : run ctx.program fuel ctx.indices.entry 0 (productArgs left right output) frame [] entered =
      .ok (final, []) := by
    simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using invoked
  exact ⟨fuel, final, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live ran, result⟩

theorem multiply_checked_contract (ctx : Context alternative) (word : WordContract ctx.program ctx.indices.word)
    (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage) :
    WrappingBinaryContract (· * ·) ctx.program ctx.indices.entry := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, result⟩ := multiply_checked_result ctx word top memory left right output call
  exact ⟨fuel, final, certificate, result.value, result.writable, result.footprint⟩
#print axioms multiply_checked_result
#print axioms multiply_checked_contract
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety

theorem scalar_correctness (ctx : Context alternative)
    (wordFound : ctx.program[ctx.indices.word]? = some (scalarWordBody ctx.profile))
    (bmi : ctx.profile.bmi2 = false) (arm : ctx.profile.armBase64 = false)
    (avx512 : ctx.profile.avx512DQVL = false) (avx2 : ctx.profile.avx2 = false) :
    WrappingBinaryContract (· * ·) ctx.program ctx.indices.entry := by
  apply multiply_checked_contract ctx ?_
    (Full.scalar_top_contract_order ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage ctx.full avx512 avx2)
  intro memory a b output wf writable
  obtain ⟨final, invoked, valid, loaded, authority, outside⟩ :=
    scalar_word_invoke ctx.profile bmi arm ctx.program ctx.indices.word wordFound memory a b output wf writable
  exact ⟨9, final, invoked, valid, loaded, authority, fun id _ offset bound => outside id offset bound⟩
#print axioms scalar_correctness
end UInt256Proof.Multiply.Entry
namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety

theorem output_encoded (memory : Memory) (output : Reference) (value : BitVec 256)
    (readable : ∃ bytes, read memory output 32 1 = .ok bytes)
    (result : inputValue memory output = value) :
    read memory output 32 1 = .ok (numberBytes value.toNat 32) := by
  obtain ⟨bytes, loaded⟩ := readable
  have length : bytes.length = 32 := by rw [read_result_snapshot loaded]; simp
  have decoded := (output_snapshot_value memory output bytes loaded).trans result
  have roundtrip := vector256_bytes_roundtrip bytes length
  rw [decoded] at roundtrip
  rw [roundtrip]
  exact loaded

theorem initialized_result (ctx : Context alternative) (word : Calls.WordContract ctx.program ctx.indices.word)
    (top : Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage) :
    UInt256Model.Safety.AggregateReturn.InitializedBinaryResult (· * ·) ctx.program ctx.indices.entry := by
  intro memory left right output call
  obtain ⟨fuel, final, cert, result⟩ := multiply_checked_result ctx word top memory left right output call
  exact ⟨fuel, final, cert, output_encoded final output _ result.readable result.value,
    result.writable, result.footprint⟩

#print axioms output_encoded
#print axioms initialized_result
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety

theorem scalar_word_contract (ctx : Context alternative)
    (wordFound : ctx.program[ctx.indices.word]? = some (scalarWordBody ctx.profile))
    (bmi : ctx.profile.bmi2 = false) (arm : ctx.profile.armBase64 = false) :
    Calls.WordContract ctx.program ctx.indices.word := by
  intro memory a b output wf writable
  obtain ⟨final, invoked, valid, loaded, authority, outside⟩ :=
    scalar_word_invoke ctx.profile bmi arm ctx.program ctx.indices.word wordFound memory a b output wf writable
  exact ⟨9, final, invoked, valid, loaded, authority, fun id _ offset bound => outside id offset bound⟩

theorem scalar_initialized_result (ctx : Context alternative)
    (wordFound : ctx.program[ctx.indices.word]? = some (scalarWordBody ctx.profile))
    (bmi : ctx.profile.bmi2 = false) (arm : ctx.profile.armBase64 = false)
    (avx512 : ctx.profile.avx512DQVL = false) (avx2 : ctx.profile.avx2 = false) :
    UInt256Model.Safety.AggregateReturn.InitializedBinaryResult (· * ·) ctx.program ctx.indices.entry :=
  initialized_result ctx (scalar_word_contract ctx wordFound bmi arm)
    (Full.scalar_top_contract_order ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage ctx.full avx512 avx2)
#print axioms scalar_initialized_result
end UInt256Proof.Multiply.Entry



