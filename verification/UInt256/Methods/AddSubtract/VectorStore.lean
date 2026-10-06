import UInt256.Methods.AddSubtract.VectorOutputMemory

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Execute a fetched vector binary operation and caller-output store, preserving
    all private snapshots even when the output overlaps the original inputs. -/
theorem vector_store_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (pc leftIndex rightIndex : Nat) (operation : CIL.Intrinsic) (value : BitVec 256)
    (available : operation.available vectorBody.profile = true)
    (differenceHome incomingHome : Reference) (difference incoming : BitVec 256)
    (differenceSlot : frame.locals[leftIndex]? = some (.bytes .vector256 differenceHome))
    (incomingSlot : frame.locals[rightIndex]? = some (.bytes .vector256 incomingHome))
    (differenceRead : read current differenceHome 32 1 = .ok (numberBytes difference.toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (evaluated : CIL.evalIntrinsic operation [.v256 difference, .v256 incoming] = some (.v256 value))
    (fetchLeft : vectorBody.code[pc]? = some (.local leftIndex))
    (fetchRight : vectorBody.code[pc + 1]? = some (.local rightIndex))
    (fetchOperation : vectorBody.code[pc + 2]? = some (.intrinsic operation 2))
    (fetchStore : vectorBody.code[pc + 3]? = some (.memory .store256))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes value.toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (pc + 4) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex pc args frame [.reference (.address output)] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs output value call currentCall outputMember authority
  have done := continuation after readback afterCall
    afterAuthority outside privateReads advanced
  have loadDifference := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 difference) difference.toNat rfl differenceSlot differenceRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 incoming) incoming.toNat rfl incomingSlot incomingRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  apply run_next_exists post found fetchLeft (loadDifference _ _)
  apply run_next_exists post found fetchRight (loadIncoming _ _)
  apply run_next_exists (target := pc + 3)
    (values := [.scalar (.v256 value), .reference (.address output)])
    (nextFrame := frame) (updated := current) post found fetchOperation
  · simp [step, pureArity, scalars, CIL.step, available, evaluated, checkedValue,
      numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · apply run_next_exists (target := pc + 4) (values := [])
      (nextFrame := frame) (updated := after) post found fetchStore
    · simp [step, staticInstruction, memoryInstruction, storeValue, referenceAt,
        written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · exact done

#print axioms vector_store_checked
end UInt256Proof.AddSubtract.Safety
