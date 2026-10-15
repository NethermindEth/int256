import CIL.Safety.CallComposition
import UInt256.Methods.Add.StorageContract

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- Use the actual extracted storage contract at a fetched call, retaining the
    caller's chosen postcondition and deriving a sufficient total fuel. -/
theorem run_store_limbs_readable {method pc : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack rest : List Value} {frame : Frame} {memory updated : Memory}
    (inputs : List Reference) (output : Reference) (w0 w1 w2 w3 : BitVec 64)
    (post : Memory → List Value → Prop)
    (methodFound : Extracted.program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call Extracted.storeLimbsIndex
      (storageArguments output w0 w1 w2 w3) rest updated))
    (call : CallingConditions Extracted.program updated inputs [output])
    (continuation : ∀ stored,
      CallingConditions Extracted.program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = updated.cells id offset) →
      AccessBelow updated.nextIdentity updated stored →
      inputValue stored output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) →
      (∃ bytes, read stored output 32 1 = .ok bytes) →
      ∃ fuel result values,
        run Extracted.program fuel method (pc + 1) args frame rest stored = .ok (result, values) ∧
        post result values) :
    ∃ fuel result values,
      run Extracted.program fuel method pc args frame stack memory = .ok (result, values) ∧
      post result values := by
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, readable⟩ :=
    store_limbs_readable_contract updated inputs output w0 w1 w2 w3 call
  have selected : storageIndex = Extracted.storeLimbsIndex := by rfl
  rw [selected] at invoked
  obtain ⟨parentFuel, result, values, resumed, satisfied⟩ := continuation stored valid outside authority value readable
  have resumed' : run Extracted.program parentFuel method (pc + 1) args frame ([] ++ rest) stored =
      .ok (result, values) := resumed
  obtain ⟨fuel, finished⟩ := run_call_exists methodFound instructionFound stepped
    ⟨childFuel, invoked⟩ ⟨parentFuel, resumed'⟩
  exact ⟨fuel, result, values, finished, satisfied⟩

theorem run_store_limbs {method pc : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack rest : List Value} {frame : Frame} {memory updated : Memory}
    (inputs : List Reference) (output : Reference) (w0 w1 w2 w3 : BitVec 64)
    (post : Memory → List Value → Prop)
    (methodFound : Extracted.program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call Extracted.storeLimbsIndex
      (storageArguments output w0 w1 w2 w3) rest updated))
    (call : CallingConditions Extracted.program updated inputs [output])
    (continuation : ∀ stored,
      CallingConditions Extracted.program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = updated.cells id offset) →
      AccessBelow updated.nextIdentity updated stored →
      inputValue stored output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) →
      ∃ fuel result values,
        run Extracted.program fuel method (pc + 1) args frame rest stored = .ok (result, values) ∧
        post result values) :
    ∃ fuel result values,
      run Extracted.program fuel method pc args frame stack memory = .ok (result, values) ∧
      post result values := by
  apply run_store_limbs_readable inputs output w0 w1 w2 w3 post
    methodFound instructionFound stepped call
  intro stored valid outside authority value _
  exact continuation stored valid outside authority value

#print axioms run_store_limbs_readable
#print axioms run_store_limbs

end UInt256Proof.Safety
