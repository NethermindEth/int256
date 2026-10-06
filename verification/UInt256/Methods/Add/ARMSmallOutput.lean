import UInt256.Methods.Add.ARMSmallFinish
import UInt256.Methods.Add.StorageCall

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- The actual storage invocation preserves the private byte flag, then the
    helper returns that same initialized scalar and retires its frame. -/
theorem arm_small_store_return (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (inputs : List Reference)
    (output flagHome : Reference) (words : Fin 4 → BitVec 64) (flag : BitVec 32)
    (call : CallingConditions Extracted.program memory inputs [output])
    (fits : localNumber .byte (.i32 flag) = .ok flag.toNat)
    (flagSlot : frame.locals[6]? = some (.bytes .byte flagHome))
    (flagRead : read memory flagHome 1 1 = .ok (numberBytes flag.toNat 1))
    (flagOld : flagHome.allocation < memory.nextIdentity)
    (privateFlag : flagHome.allocation ≠ output.allocation)
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored,
      CallingConditions Extracted.program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = memory.cells id offset) →
      AccessBelow memory.nextIdentity memory stored →
      inputValue stored output = UInt256Model.value words →
      post (leaveFrame frame stored) [.scalar (.i32 flag)]) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 52 args frame
        [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory =
            .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have formed := call.output_formed (by simp : output ∈ [output])
    apply run_store_limbs inputs output (words 0) (words 1) (words 2) (words 3) post
      (body := Extracted.addScalarUInt64Body) (op := .call Extracted.storeLimbsIndex 5)
    · rfl
    · rfl
    · unfold storageArguments
      repeat' (conv in storageWordOrder => cbv)
      simp [List.range_succ, List.findIdx, List.findIdx.go, step, checkedValue, numericValue, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl⟩
    · exact call
    · intro stored valid outside authority value
      have retained : read stored flagHome 1 1 = .ok (numberBytes flag.toNat 1) := by
        apply authority.read_eq flagRead flagOld
        intro i bound
        exact outside _ _ (Or.inl privateFlag)
      refine ⟨2, leaveFrame frame stored, [.scalar (.i32 flag)], ?_, ?_⟩
      · exact arm_small_return enabled stored frame args flagHome flag fits flagSlot retained
      · apply continuation stored valid outside authority
        simpa only [UInt256Model.value] using value

#print axioms arm_small_store_return
end UInt256Proof.Add.Safety
