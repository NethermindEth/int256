import UInt256.Methods.Add.Vector128RepairDispatch
import UInt256.Methods.Add.CarryCall
import UInt256.Safety.LimbAccess
import UInt256.Methods.Add.CarryState

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Initialize the private carry word before the SSE scalar repair cascade. -/
theorem vector128_sse_repair_start (disabled : Extracted.profile.advSimd = false)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[15]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes 0 8) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes 0 8) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 165 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 162 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at disabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 14 ⟨.word64, .i64 0, 0, rfl⟩ (by rfl) (.i64 0) 0 rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, pureArity, scalars, CIL.step, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_sse_repair_start
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_sse_carry_segment (disabled : Extracted.profile.advSimd = false) (segment : Fin 4) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (a b : BitVec 64) (carryHome resultHome : Reference)
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right)
    (leftRead : ∀ rest, instruction (.field segment)
      (.reference (.address left) :: rest) memory = .ok (memory, .scalar (.i64 a) :: rest))
    (rightRead : ∀ rest, instruction (.field segment)
      (.reference (.address right) :: rest) memory = .ok (memory, .scalar (.i64 b) :: rest))
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[segment.val + 16]? = some (.bytes .word64 resultHome))
    (carryFormed : form memory carryHome = .ok carryHome)
    (resultFormed : form memory resultHome = .ok resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (171 + 7 * segment.val)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (165 + 7 * segment.val)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  first
  | solve | simp [Extracted.profile] at disabled
  |
    obtain ⟨segment, bound⟩ := segment
    have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      dsimp at leftRead rightRead resultSlot
      first
      | change frame.locals[16]? = some (.bytes .word64 resultHome) at resultSlot
      | change frame.locals[17]? = some (.bytes .word64 resultHome) at resultSlot
      | change frame.locals[18]? = some (.bytes .word64 resultHome) at resultSlot
      | change frame.locals[19]? = some (.bytes .word64 resultHome) at resultSlot
      repeat'
        first
        | exact continuation
        | simp (config := { failIfUnchanged := false })
          apply run_next_exists post (by rfl : Extracted.program[vector128Index]? = some vector128Body) (by rfl)
          simp (config := { implicitDefEqProofs := false })
              [cil_code, step, checkedValue, formValue, leftFormed, rightFormed,
                carryFormed, resultFormed, carrySlot, resultSlot, localAddress, leftRead, rightRead,
                pureArity, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩


#print axioms vector128_sse_carry_segment
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_sse_indexed_carry (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (carryHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes c.toNat 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, CarryPost a b c carryHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (172 + 7 * index.val) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (171 + 7 * index.val) args frame
        [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have carryFormed := access_reference_valid _ _ _ _ _ carryWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  apply run_carry_call a b c carryHome resultHome post (body := vector128Body)
    (op := .call Extracted.addWithCarryIndex 4)
  · rfl
  · obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals rfl
  · simp [step, checkedValue, numericValue, formValue, carryFormed, resultFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact wellFormed
  · exact incoming
  · exact carryRead
  · exact carryWrite
  · exact resultWrite
  · exact disjoint
  · simpa only [show 171 + 7 * index.val + 1 = 172 + 7 * index.val by omega] using continuation

#print axioms vector128_sse_indexed_carry

open UInt256Model.Safety

/-- Valid caller views discharge both field loads for each remaining limb;
    checked home accesses discharge address formation and the mathematical call. -/
theorem vector128_sse_carry_segment_checked (segment : Fin 4) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : CIL.Safety.Memory) (c : BitVec 64) (carryHome resultHome : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[segment.val + 16]? = some (.bytes .word64 resultHome))
    (incoming : c.toNat ≤ 1)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes c.toNat 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      CarryPost (inputLimb memory left segment)
        (inputLimb memory right segment) c carryHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (172 + 7 * segment.val)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (165 + 7 * segment.val)
        (binaryArguments left right output ++ extra) frame [] memory = .ok (result, returned) ∧ post result returned := by
  apply vector128_sse_carry_segment (by rfl) segment left right output extra frame memory _ _ carryHome resultHome
    (call.input_formed (by simp)) (call.input_formed (by simp))
    (fun rest => call.input_field_instruction (by simp) _ rest)
    (fun rest => call.input_field_instruction (by simp) _ rest) carrySlot resultSlot
    (access_reference_valid _ _ _ _ _ carryWrite) (access_reference_valid _ _ _ _ _ resultWrite) post
  exact vector128_sse_indexed_carry segment (binaryArguments left right output ++ extra)
    frame memory _ _ c carryHome resultHome call.1.1 incoming carryRead carryWrite resultWrite disjoint post continuation

#print axioms vector128_sse_carry_segment_checked

end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

/-- Advance the shared carry invariant through one actual SSE repair call. -/
theorem vector128_sse_carry_next {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarCarryState original before frame left right output carryHome results index.val 15 16)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results (index.val + 1) 15 16 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (172 + 7 * index.val)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (165 + 7 * index.val)
        (binaryArguments left right output ++ extra) frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_sse_carry_segment_checked index left right output extra frame before
    (scalarCarryValue original left right index.val) carryHome (results index) state.call
    state.carrySlot (state.resultSlots index) state.carryBound state.carryRead state.carryWrite
    (state.resultWrites index) (Or.inl (Ne.symm (state.carrySeparate index))) post
  intro after math
  apply continuation after
  apply state.advance index
  simpa only [inputLimb, state.inputBytes left (by simp), state.inputBytes right (by simp)] using math

/-- All four carry calls retain the initial operands, checked private homes and
    every completed result limb, even when caller input and output views overlap. -/
theorem vector128_sse_carry_all {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarCarryState original before frame left right output carryHome results 0 15 16)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState original after frame left right output carryHome results 4 15 16 →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 193 (binaryArguments left right output ++ extra)
          frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 165 (binaryArguments left right output ++ extra)
        frame [] before = .ok (result, returned) ∧ post result returned := by
  apply vector128_sse_carry_next 0 state extra post
  intro _ first
  apply vector128_sse_carry_next 1 first extra post
  intro _ second
  apply vector128_sse_carry_next 2 second extra post
  intro _ third
  exact vector128_sse_carry_next 3 third extra post continuation

#print axioms vector128_sse_carry_next
#print axioms vector128_sse_carry_all
end UInt256Proof.Add.Safety
