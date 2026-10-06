import UInt256.Methods.Add.ARMSmallReady

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Distinct extracted numeric slots have distinct allocation identities. -/
theorem arm_small_other_read {entered before after : Memory} {boundary : Nat}
    {slots : List LocalSlot} (homes : NumericHomes entered boundary armSmallSpecs slots)
    {i j : Nat} (different : i ≠ j) {source target : Reference}
    {sourceKind targetKind : CIL.LocalKind}
    (sourceSlot : slots[i]? = some (.bytes sourceKind source))
    (targetSlot : slots[j]? = some (.bytes targetKind target))
    {bytes value : List (BitVec 8)} {width : Nat}
    (written : write before target bytes 1 = .ok after)
    (loaded : read before source width 1 = .ok value) :
    read after source width 1 = .ok value := by
  by_cases earlier : i < j
  · exact write_preserves_disjoint_read written loaded
      (Or.inl (Nat.ne_of_lt (homes.ordered i j sourceKind targetKind source target earlier sourceSlot targetSlot)))
  · exact write_preserves_disjoint_read written loaded
      (Or.inl (Nat.ne_of_gt (homes.ordered j i targetKind sourceKind target source (by omega) targetSlot sourceSlot)))

structure ARMSmallState (original entered current : Memory) (input output : Reference)
    (frame : Frame) (words : Fin 4 → BitVec 64) (sum : BitVec 64) (flag : BitVec 32) : Prop where
  call : CallingConditions Extracted.program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  limbs : ∀ i : Fin 4, ∃ home, frame.locals[i.val]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes (words i).toNat 8)
  sumRead : ∃ home, frame.locals[5]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes sum.toNat 8)
  flagRead : ∃ home, frame.locals[6]? = some (.bytes .byte home) ∧
    read current home 1 1 = .ok (numberBytes flag.toNat 1)
  flagFits : localNumber .byte (.i32 flag) = .ok flag.toNat

theorem ARMSmallReady.state {original entered current : Memory} {input output : Reference}
    {word : BitVec 64} {frame : Frame}
    (ready : ARMSmallReady original entered current input output word frame) :
    ARMSmallState original entered current input output frame (inputLimb original input)
      (inputLimb original input 0 + word) 0 :=
  ⟨ready.saved.call, ready.saved.preserved, ready.saved.authority,
    fun i => ready.saved.completed i i.isLt, ready.sum, ready.flag, rfl⟩

/-- Updating one saved limb derives the actual store and preserves all remaining
    initialized homes, including the low sum and the one-byte flag. -/
theorem ARMSmallState.store_limb {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState original entered current input output frame words sum flag)
    (index : Fin 4) (value : BitVec 64) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after,
      ARMSmallState original entered after input output frame
        (fun i => if i = index then value else words i) sum flag ∧
      ∀ pc args rest, step Extracted.addScalarUInt64Body (.setLocal index.val) pc args frame
        (.scalar (.i64 value) :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨home, after, slot, loaded, preserved, call, authority, written, stepped⟩ :=
    arm_small_private_store original.nextIdentity entered current [input] [output] frame
      state.call enteredWF homes state.authority index.val armSmallWordSpec (arm_small_input_spec index)
      (.i64 value) value.toNat rfl
  refine ⟨after, ⟨call, state.preserved.trans preserved, authority, ?_, ?_, ?_, state.flagFits⟩, stepped⟩
  · intro i
    by_cases same : i = index
    · subst i
      exact ⟨home, slot, by simpa [armSmallWordSpec, localWidth] using loaded⟩
    · obtain ⟨other, otherSlot, otherRead⟩ := state.limbs i
      refine ⟨other, otherSlot, ?_⟩
      simp only [same, ite_false]
      exact arm_small_other_read homes (fun h => same (Fin.ext h)) otherSlot slot written otherRead
  · obtain ⟨other, otherSlot, otherRead⟩ := state.sumRead
    exact ⟨other, otherSlot, arm_small_other_read homes (by omega) otherSlot slot written otherRead⟩
  · obtain ⟨other, otherSlot, otherRead⟩ := state.flagRead
    exact ⟨other, otherSlot, arm_small_other_read homes (by omega) otherSlot slot written otherRead⟩


/-- Updating the byte flag preserves all limb and sum snapshots. -/
theorem ARMSmallState.store_flag (enabled : Extracted.profile.advSimd = true)
    {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState original entered current input output frame words sum flag)
    (value : BitVec 32) (fits : localNumber .byte (.i32 value) = .ok value.toNat)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals) :
    ∃ after, ARMSmallState original entered after input output frame words sum value ∧
      ∀ pc args rest, step Extracted.addScalarUInt64Body (.setLocal 6) pc args frame
        (.scalar (.i32 value) :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨home, after, slot, loaded, preserved, call, authority, written, stepped⟩ :=
      arm_small_private_store original.nextIdentity entered current [input] [output] frame
        state.call enteredWF homes state.authority 6 ⟨.byte, .i32 0, 0, rfl⟩ (by rfl)
        (.i32 value) value.toNat fits
    refine ⟨after, ⟨call, state.preserved.trans preserved, authority, ?_, ?_,
      ⟨home, slot, loaded⟩, fits⟩, stepped⟩
    · intro i
      obtain ⟨other, otherSlot, otherRead⟩ := state.limbs i
      exact ⟨other, otherSlot, arm_small_other_read homes (by omega) otherSlot slot written otherRead⟩
    · obtain ⟨other, otherSlot, otherRead⟩ := state.sumRead
      exact ⟨other, otherSlot, arm_small_other_read homes (by decide : 5 ≠ 6) otherSlot slot written otherRead⟩

/-- Execute one carry increment with every memory premise derived from the state. -/
theorem ARMSmallState.increment (enabled : Extracted.profile.advSimd = true)
    {original entered current : Memory} {input output : Reference}
    {frame : Frame} {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState original entered current input output frame words sum flag)
    (segment : Fin 3) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ARMSmallState original entered after input output frame
        (fun i => if i = (⟨segment.val + 1, by omega⟩ : Fin 4)
          then words ⟨segment.val + 1, by omega⟩ + 1 else words i) sum flag →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index (29 + 7 * segment.val) args frame
          [.scalar (.i64 (words ⟨segment.val + 1, by omega⟩ + 1))] after =
            .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (23 + 7 * segment.val) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  obtain ⟨home, slot, loaded⟩ := state.limbs index
  obtain ⟨after, updated, stored⟩ := state.store_limb index (words index + 1) enteredWF homes
  exact arm_small_increment enabled segment current after frame args home (words index) slot loaded
    (fun pc rest => stored pc args rest) post (continuation after updated)

#print axioms ARMSmallState.store_flag
#print axioms ARMSmallState.increment

#print axioms arm_small_other_read
#print axioms ARMSmallReady.state
#print axioms ARMSmallState.store_limb
end UInt256Proof.Add.Safety
