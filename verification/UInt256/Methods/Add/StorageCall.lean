import CIL.Safety.CallComposition
import CIL.Safety.AccessBelow
import UInt256.Safety.Calling
import UInt256.Safety.OutputAccess

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- The checked contract a parent needs from its four-limb storage helper: each extraction
    proves it from its own helper body and argument order. -/
def LimbStorageContract (program : CIL.Program) (index : Nat)
    (arguments : Reference → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → List Value) : Prop :=
  ∀ (memory : Memory) (inputs : List Reference) (output : Reference) (w0 w1 w2 w3 : BitVec 64),
    CallingConditions program memory inputs [output] →
    ∃ fuel result,
      invoke program fuel index (arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read result output 32 1 = .ok bytes)

variable {program : CIL.Program} {index : Nat}
  {arguments : Reference → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → List Value}

/-- Use the checked storage contract at a fetched call, retaining the caller's chosen
    postcondition and deriving a sufficient total fuel. -/
theorem run_store_limbs_readable (contract : LimbStorageContract program index arguments)
    {method pc : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack rest : List Value} {frame : Frame} {memory updated : Memory}
    (inputs : List Reference) (output : Reference) (w0 w1 w2 w3 : BitVec 64)
    (post : Memory → List Value → Prop)
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call index
      (arguments output w0 w1 w2 w3) rest updated))
    (call : CallingConditions program updated inputs [output])
    (continuation : ∀ stored,
      CallingConditions program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = updated.cells id offset) →
      AccessBelow updated.nextIdentity updated stored →
      inputValue stored output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) →
      (∃ bytes, read stored output 32 1 = .ok bytes) →
      ∃ fuel result values,
        run program fuel method (pc + 1) args frame rest stored = .ok (result, values) ∧
        post result values) :
    ∃ fuel result values,
      run program fuel method pc args frame stack memory = .ok (result, values) ∧
      post result values := by
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, readable⟩ :=
    contract updated inputs output w0 w1 w2 w3 call
  obtain ⟨parentFuel, result, values, resumed, satisfied⟩ := continuation stored valid outside authority value readable
  have resumed' : run program parentFuel method (pc + 1) args frame ([] ++ rest) stored =
      .ok (result, values) := resumed
  obtain ⟨fuel, finished⟩ := run_call_exists methodFound instructionFound stepped
    ⟨childFuel, invoked⟩ ⟨parentFuel, resumed'⟩
  exact ⟨fuel, result, values, finished, satisfied⟩

theorem run_store_limbs (contract : LimbStorageContract program index arguments)
    {method pc : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack rest : List Value} {frame : Frame} {memory updated : Memory}
    (inputs : List Reference) (output : Reference) (w0 w1 w2 w3 : BitVec 64)
    (post : Memory → List Value → Prop)
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call index
      (arguments output w0 w1 w2 w3) rest updated))
    (call : CallingConditions program updated inputs [output])
    (continuation : ∀ stored,
      CallingConditions program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = updated.cells id offset) →
      AccessBelow updated.nextIdentity updated stored →
      inputValue stored output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) →
      ∃ fuel result values,
        run program fuel method (pc + 1) args frame rest stored = .ok (result, values) ∧
        post result values) :
    ∃ fuel result values,
      run program fuel method pc args frame stack memory = .ok (result, values) ∧
      post result values := by
  apply run_store_limbs_readable contract inputs output w0 w1 w2 w3 post
    methodFound instructionFound stepped call
  intro stored valid outside authority value _
  exact continuation stored valid outside authority value

#print axioms run_store_limbs_readable
#print axioms run_store_limbs

end UInt256Proof.Safety
