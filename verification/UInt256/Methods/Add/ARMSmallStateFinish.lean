import UInt256.Methods.Add.ARMSmallState

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armSmallOutputWords (words : Fin 4 → BitVec 64) (sum : BitVec 64) : Fin 4 → BitVec 64 :=
  fun i => if i.val = 0 then sum else words i

theorem ARMSmallState.final_flag (enabled : Extracted.profile.advSimd = true)
    {original entered current : Memory} {input output : Reference} {frame : Frame}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState original entered current input output frame words sum flag)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ARMSmallState original entered after input output frame words sum
        (if words 3 = BitVec.ofNat 64 0 then 1 else 0) →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index 47 args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 43 args frame [.scalar (.i64 (words 3))] current =
        .ok (final, returned) ∧ post final returned := by
  let bit : BitVec 32 := if words 3 = BitVec.ofNat 64 0 then 1 else 0
  have fits : localNumber .byte (.i32 bit) = .ok bit.toNat := by
    dsimp only [bit]
    split <;> rfl
  obtain ⟨after, updated, stored⟩ := state.store_flag enabled bit fits enteredWF homes
  exact arm_small_final_flag enabled current after frame args (words 3) (stored 46 args [])
    post (continuation after updated)

/-- Every output argument and the flag read are derived from the carry state.
    Private/caller separation follows from actual allocation bounds. -/
theorem ARMSmallState.output (enabled : Extracted.profile.advSimd = true)
    {original entered current : Memory} {input output : Reference} {frame : Frame}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64} {flag : BitVec 32}
    (state : ARMSmallState original entered current input output frame words sum flag)
    (args : List Value) (argument : args[2]? = some (.reference (.address output)))
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (homes : NumericHomes entered original.nextIdentity armSmallSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored,
      CallingConditions Extracted.program stored [input] [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = current.cells id offset) →
      AccessBelow current.nextIdentity current stored →
      inputValue stored output = UInt256Model.value (armSmallOutputWords words sum) →
      post (leaveFrame frame stored) [.scalar (.i32 flag)]) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 47 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  classical
  have candidates : ∀ i : Fin 4, ∃ home,
      frame.locals[if i.val = 0 then 5 else i.val]? = some (.bytes .word64 home) ∧
      read current home 8 1 = .ok (numberBytes (armSmallOutputWords words sum i).toNat 8) := by
    intro i
    by_cases zero : i.val = 0
    · simpa only [armSmallOutputWords, zero, ite_true] using state.sumRead
    · simpa only [armSmallOutputWords, zero, ite_false] using state.limbs i
  let outputHomes := fun i => Classical.choose (candidates i)
  have facts := fun i => Classical.choose_spec (candidates i)
  apply arm_small_output_arguments enabled current frame args output outputHomes
    (armSmallOutputWords words sum) (fun i => (facts i).1) (fun i => (facts i).2)
    argument (state.call.output_formed (by simp)) post
  obtain ⟨flagHome, flagSlot, flagRead⟩ := state.flagRead
  have fresh := homes.home_bound 6 .byte flagHome flagSlot
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (read_reference_valid _ _ _ _ _ flagRead)
  have flagOld := (state.call.1.1.1 _ _ present).1
  obtain ⟨outAllocation, outPresent, _, _⟩ := formed_reference_live _ _ _
    (originalCall.output_formed (by simp : output ∈ [output]))
  have outputOld : output.allocation < original.nextIdentity := (originalCall.1.1.1 _ _ outPresent).1
  exact arm_small_store_return enabled current frame args [input] output flagHome
    (armSmallOutputWords words sum) flag state.call state.flagFits flagSlot flagRead flagOld
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le outputOld fresh)) post continuation

#print axioms ARMSmallState.final_flag
#print axioms ARMSmallState.output
end UInt256Proof.Add.Safety
