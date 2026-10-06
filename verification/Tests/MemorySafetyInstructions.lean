import CIL.Safety.AccessAlignment
import UInt256.Safety.OutputInitialization
import UInt256.Safety.OrderedScalarProfiles
import UInt256.Safety.ReadOnlyCall
import UInt256.Safety.BinaryReturn
import UInt256.Safety.OutputEncoding
import CIL.Safety.RelocationExecution
import CIL.Safety.StaticMemoryBelow
import CIL.Safety.ArgumentEquivalence
import CIL.Safety.WordFrameSetup
import CIL.Safety.NegationReturn
import CIL.Safety.ProfileEquivalence
import UInt256.Safety.ProfileContracts
import UInt256.Safety.ScalarOperatorResult
import UInt256.Safety.ScalarValueContract
import UInt256.Safety.ReportingContract
import UInt256.Safety.PrivateCalls
import CIL.Safety.WordPrefix
import UInt256.Safety.Contract
import UInt256.Safety.InitializedOutput
import UInt256.Safety.UnaryOutput
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.ReadOnlyExecution
import UInt256.Safety.ReadOnlyForwarder
import UInt256.Safety.ReadOnlyScalarExecution
import UInt256.Safety.ScalarEqualityFacts
import UInt256.Safety.HalfAccess
import UInt256.Safety.ArgumentValues
import CIL.Safety.ConstructComposition
import CIL.Safety.ConstructSetup
import CIL.Safety.NumericLocalStore
import CIL.Safety.NumericLocalLoad
import CIL.Safety.NumericHomes
import UInt256.Safety.FourLimbWrites
import UInt256.Safety.OutputLoad
import UInt256.Safety.ConstructorSetup
import UInt256.Safety.PrivateAggregateStore
import CIL.Safety.AccessBelow
import CIL.Safety.WordFootprint
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory
import CIL.Safety.WordLocals
import CIL.Safety.CallComposition
import Tests.MemorySafety
import UInt256.Safety.CallerExamples
import UInt256.Safety.CallerSetup
import UInt256.Safety.OutputValue
import CIL.Safety.FrameProgress
import CIL.Safety.InstructionMemoryLemmas
import CIL.Safety.Execution
import CIL.Safety.FrameLemmas
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.FrameOwnership
import CIL.Safety.FrameAllocations
import CIL.Safety.ExecutionLemmas
import CIL.Safety.ExecutionInvariants
import CIL.Safety.ExecutionPrefixes
import CIL.Safety.ExecutionLifetime
import CIL.Safety.ExecutionFrameOwnership
import CIL.Safety.FuelLemmas
import CIL.Safety.StaticMemoryLemmas
import CIL.Safety.StaticWorld
import CIL.Safety.StaticLifetime
import CIL.Safety.StaticInstructionWorld
import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.LiveState
import CIL.Safety.StaticReferences
import CIL.Safety.StepLiveState
import CIL.Safety.RunReturnTrace

namespace CIL.Safety.Tests

theorem actual_scalar_load : loadValue initial (.address ⟨0, 8⟩) 8 = .ok (.i64 1) := by rfl

theorem canonical_boolean_bitcasts :
    memoryInstruction .bitcastByteBool [.scalar (.i8 0)] initial =
      .ok (initial, [.scalar (.i32 0)]) ∧
    memoryInstruction .bitcastByteBool [.scalar (.i32 1)] initial =
      .ok (initial, [.scalar (.i32 1)]) := by exact ⟨rfl, rfl⟩

theorem noncanonical_boolean_bitcasts_rejected :
    memoryInstruction .bitcastByteBool [.scalar (.i8 255)] initial =
      .error (.unsupported "Noncanonical Boolean representation") ∧
    memoryInstruction .bitcastByteBool [.scalar (.i32 2)] initial =
      .error (.unsupported "Noncanonical Boolean representation") := by exact ⟨rfl, rfl⟩

#print axioms canonical_boolean_bitcasts
#print axioms noncanonical_boolean_bitcasts_rejected

theorem actual_overread_discarded :
    instructions [.memory .load256, .pop] [.reference (.address ⟨0, 16⟩)] initial =
      .error (.memory .outsideAllocation (.address ⟨0, 16⟩) 32) := by rfl

theorem actual_invalid_reference_then_repaired :
    instructions [.const32 (BitVec.ofInt 32 (-1)), .memory (.add 8 true),
      .const32 1, .memory (.add 8 true), .pop] [.reference (.address source)] initial =
      .error (.memory .invalidReference (.address source) 0) := by rfl

theorem actual_forbidden_write_then_restored :
    instructions [.const64 0, .store64, .const64 0, .store64]
      [.reference (.address source), .reference (.address source)] initial =
      .error (.memory .unwritable (.address source) 8) := by rfl

theorem actual_partial_vector_initialization :
    instructions [.memory .load256, .pop]
      [.reference (.address target)] { initial with views := [⟨0, 0, 40, true, true⟩] } =
      .error (.memory .uninitialized (.address target) 32) := by rfl

theorem actual_expired_field_address :
    instruction (.fieldAddr ⟨1, by decide⟩) [.reference (.address source)] (expire initial 0) =
      .error (.memory .expiredLifetime (.address source) 0) := by rfl

theorem actual_signed_offset_preserves_origin :
    match instruction (.memory (.add 8 true)) [.scalar (.i32 (BitVec.ofInt 32 (-1))),
        .reference (.address target)] initial with
    | .error _ => False
    | .ok (_, values) => values = [.reference (.address source)] := by rfl

theorem actual_reference_cast_keeps_origin :
    match instruction (.memory .asRef) [.reference (.address target)] initial with
    | .error _ => False
    | .ok (_, values) => values = [.reference (.address target)] := by rfl

theorem actual_fault_location :
    instructionAt 4 17 .load64 [.reference .null] initial =
      .error ⟨4, 17, .memory .nullDereference .null 8⟩ := by rfl

theorem actual_vector_snapshot_copy :
    match instructions [.memory .load256, .memory .store256]
        [.reference (.address source), .reference (.address target)] initial with
    | .error _ => False
    | .ok (final, values) => values = [] ∧ final.cells 0 16 = ⟨1, true⟩ ∧
        (final.cells 0 32).initialized = true := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms actual_overread_discarded
#print axioms actual_invalid_reference_then_repaired
#print axioms actual_forbidden_write_then_restored
#print axioms actual_partial_vector_initialization
#print axioms actual_expired_field_address
#print axioms actual_vector_snapshot_copy
#print axioms CIL.Safety.instruction_fault_cannot_be_erased
#print axioms CIL.Safety.successful_instruction_prefix

def localCopyBody : CIL.Method := {
  code := [.localAddr 0, .const64 9, .store64, .local 0, .ret]
  locals := [.i64 0]
  localKinds := [.word64]
  returnsValue := true }

theorem private_frame_preserves_caller_reference :
    match enterFrame localCopyBody [] initial with
    | .error _ => False
    | .ok (frame, memory) => form (leaveFrame frame memory) source = .ok source := by rfl

#print axioms private_frame_preserves_caller_reference
#print axioms CIL.Safety.AllocationExtension.preserves_reference

theorem local_address_aliases_local_value :
    (invoke [localCopyBody] 10 0 [] initial).map Prod.snd =
      .ok [.scalar (.i64 9)] := by rfl

def uninitializedBody : CIL.Method := {
  code := [.local 0, .ret]
  locals := [.unmodeled]
  localKinds := [.word64]
  returnsValue := true }

def callBody : CIL.Method := {
  code := [.call 1 0, .ret]
  locals := []
  returnsValue := true }

theorem nested_call_preserves_numeric_result :
    (invoke [callBody, localCopyBody] 20 0 [] initial).map Prod.snd =
      .ok [.scalar (.i64 9)] := by rfl

theorem nested_uninitialized_local_rejected :
    (invoke [callBody, uninitializedBody] 20 0 [] initial).map Prod.snd =
      .error ⟨1, 0, .memory .uninitialized (.address ⟨1, 0⟩) 8⟩ := by rfl

def escapingBody : CIL.Method := {
  code := [.localAddr 0, .ret]
  locals := [.i64 0]
  localKinds := [.word64]
  returnsValue := true }

theorem escaped_local_rejected_before_caller_resumes :
    (invoke [callBody, escapingBody] 20 0 [] initial).map Prod.snd =
      .error ⟨1, 1, .memory .expiredLifetime (.address ⟨1, 0⟩) 0⟩ := by rfl

def branchBody : CIL.Method := {
  code := [.const32 0, .brzero 3, .unsupported "must not execute", .const64 11, .ret]
  locals := []
  returnsValue := true }

theorem branch_uses_actual_instruction_target :
    (invoke [branchBody] 10 0 [] initial).map Prod.snd =
      .ok [.scalar (.i64 11)] := by rfl

theorem raw_address_cannot_be_scalar_argument :
    (invoke [branchBody] 10 0 [.scalar (.ref (.byte 0))] initial).map Prod.snd =
      .error ⟨0, 0, .invalidState⟩ := by rfl

theorem reference_local_keeps_provenance :
    storeLocal initial (.root none) (.reference (.address target)) =
      .ok (.root (some (.address target)), initial) := by rfl

#print axioms local_address_aliases_local_value
#print axioms nested_call_preserves_numeric_result
#print axioms nested_uninitialized_local_rejected
#print axioms escaped_local_rejected_before_caller_resumes
#print axioms branch_uses_actual_instruction_target
#print axioms raw_address_cannot_be_scalar_argument
#print axioms reference_local_keeps_provenance

def aggregateBody : CIL.Method := {
  code := [.aggregateArgAddr 0, .const64 5, .setField ⟨1, by decide⟩,
    .aggregateArgAddr 0, .field ⟨1, by decide⟩, .ret]
  locals := []
  aggregateArgs := [0]
  returnsValue := true }

theorem aggregate_argument_is_private_snapshot :
    match invoke [aggregateBody] 20 0 [.scalar (.v256 17)] initial with
    | .error _ => False
    | .ok (memory, values) => values = [.scalar (.i64 5)] ∧
        memory.cells 0 8 = initial.cells 0 8 := by
  exact ⟨rfl, rfl⟩

theorem aggregate_argument_loads_complete_snapshot :
    (invoke [{ aggregateBody with code := [.aggregateArg 0, .ret] }]
      10 0 [.scalar (.v256 17)] initial).map Prod.snd =
      .ok [.scalar (.v256 17)] := by rfl

def escapedAggregateBody : CIL.Method := {
  code := [.aggregateArgAddr 0, .ret]
  locals := []
  aggregateArgs := [0]
  returnsValue := true }

theorem aggregate_home_reference_cannot_escape :
    (invoke [escapedAggregateBody] 10 0 [.scalar (.v256 17)] initial).map Prod.snd =
      .error ⟨0, 1, .memory .expiredLifetime (.address ⟨1, 0⟩) 0⟩ := by rfl

def constructorBody : CIL.Method := {
  code := [.arg 0, .arg 1, .setField ⟨0, by decide⟩, .ret]
  locals := []
  returnsValue := false }

def constructBody : CIL.Method := {
  code := [.const64 7, .newValue 1 1, .ret]
  locals := []
  returnsValue := true }

theorem constructor_snapshot_survives_child_frame :
    match invoke [constructBody, constructorBody] 20 0 [] initial with
    | .error _ => False
    | .ok (memory, values) => values = [.scalar (.v256 7)] ∧
        liveAllocation memory 1 = .error .expiredLifetime := by
  exact ⟨rfl, rfl⟩

theorem constructor_cannot_return_an_unexpected_value :
    (invoke [constructBody, { constructorBody with
      code := [.const64 1, .ret]
      returnsValue := true }] 20 0 [] initial).map Prod.snd =
      .error ⟨0, 1, .invalidState⟩ := by rfl

#print axioms aggregate_argument_is_private_snapshot
#print axioms aggregate_argument_loads_complete_snapshot
#print axioms aggregate_home_reference_cannot_escape
#print axioms constructor_snapshot_survives_child_frame
#print axioms constructor_cannot_return_an_unexpected_value

theorem uninitialized_local_refutes_every_successful_fuel :
    ∀ fuel result, invoke [uninitializedBody] fuel 0 [] initial ≠ .ok result := by
  exact invoke_fault_refutes_success [uninitializedBody] 10 0 [] initial
    ⟨0, 0, .memory .uninitialized (.address ⟨1, 0⟩) 8⟩ (by decide) (by rfl)
#print axioms uninitialized_local_refutes_every_successful_fuel

def lookup : CIL.StaticDescriptor := ⟨0, "lookupA", numberBytes 42 8⟩

def staticBody : CIL.Method := {
  code := [.memory (.staticAddress lookup.bytes), .load64, .ret]
  staticSites := [(0, lookup)]
  locals := []
  returnsValue := true }

theorem static_read_uses_bound_extracted_bytes :
    (invoke [staticBody] 10 0 [] initial).map Prod.snd = .ok [.scalar (.i64 42)] := by rfl

theorem static_store_rejected :
    (invoke [{ staticBody with
      code := [.memory (.staticAddress lookup.bytes), .const64 0, .store64, .ret]
      returnsValue := false }] 10 0 [] initial).map Prod.snd =
      .error ⟨0, 2, .memory .unwritable (.address ⟨1, 0⟩) 8⟩ := by rfl

theorem missing_static_identity_rejected :
    (invoke [{ staticBody with staticSites := [] }] 10 0 [] initial).map Prod.snd =
      .error ⟨0, 0, .unsupported "Missing extracted static field identity"⟩ := by rfl

theorem static_instruction_bytes_must_match_metadata :
    (invoke [{ staticBody with staticSites := [(0, { lookup with bytes := numberBytes 43 8 })] }]
      10 0 [] initial).map Prod.snd = .error ⟨0, 0, .invalidState⟩ := by rfl

theorem distinct_static_fields_keep_distinct_identities :
    match staticReference lookup initial with
    | .error _ => False
    | .ok (memory, first) => match staticReference { lookup with identity := 1, fieldName := "lookupB" } memory with
      | .error _ => False
      | .ok (memory, second) => match staticReference lookup memory with
        | .error _ => False
        | .ok (_, repeated) => first = ⟨1, 0⟩ ∧ second = ⟨2, 0⟩ ∧ repeated = first := by
  exact ⟨rfl, rfl, rfl⟩

theorem empty_span_reference_can_be_formed :
    memoryInstruction .spanReference [.span .null 0] initial =
      .ok (initial, [.reference .null]) := by rfl

theorem empty_span_reference_cannot_be_read :
    instructions [.memory .spanReference, .load64] [.span .null 0] initial =
      .error (.memory .nullDereference .null 8) := by rfl

#print axioms static_read_uses_bound_extracted_bytes
#print axioms static_store_rejected
#print axioms missing_static_identity_rejected
#print axioms static_instruction_bytes_must_match_metadata
#print axioms distinct_static_fields_keep_distinct_identities
#print axioms empty_span_reference_can_be_formed
#print axioms empty_span_reference_cannot_be_read

end CIL.Safety.Tests
