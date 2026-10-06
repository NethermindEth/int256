import UInt256.Methods.Add.Vector128SSECarrySegments
import UInt256.Methods.Add.CarryCall
import UInt256.Safety.LimbAccess

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
