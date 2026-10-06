import UInt256.Methods.Subtract.Vector128BorrowSegments
import UInt256.Methods.Subtract.BorrowCaller
import UInt256.Safety.LimbAccess

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_indexed_borrow (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (borrowHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, BorrowPost a b c borrowHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (87 + 7 * index.val) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (86 + 7 * index.val) args frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have borrowFormed := access_reference_valid _ _ _ _ _ borrowWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  apply run_borrow_call a b c borrowHome resultHome post (body := vector128Body)
    (op := .call Extracted.subtractWithBorrowIndex 4)
  · rfl
  · obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals rfl
  · simp [step, checkedValue, numericValue, formValue, borrowFormed, resultFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact wellFormed
  · exact incoming
  · exact borrowRead
  · exact borrowWrite
  · exact resultWrite
  · exact disjoint
  · simpa only [show 86 + 7 * index.val + 1 = 87 + 7 * index.val by omega] using continuation

#print axioms vector128_indexed_borrow

open UInt256Model.Safety

/-- Valid caller views discharge both field loads for each remaining limb;
    checked home accesses discharge address formation and the mathematical call. -/
theorem vector128_borrow_segment_checked (segment : Fin 4) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : CIL.Safety.Memory) (c : BitVec 64) (borrowHome resultHome : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (borrowSlot : frame.locals[11]? = some (.bytes .word64 borrowHome))
    (resultSlot : frame.locals[segment.val + 12]? = some (.bytes .word64 resultHome))
    (incoming : c.toNat ≤ 1)
    (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowHome resultHome)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      BorrowPost (inputLimb memory left segment)
        (inputLimb memory right segment) c borrowHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (87 + 7 * segment.val)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (80 + 7 * segment.val)
        (binaryArguments left right output ++ extra) frame [] memory = .ok (result, returned) ∧ post result returned := by
  apply vector128_borrow_segment segment left right output extra frame memory _ _ borrowHome resultHome
    (call.input_formed (by simp)) (call.input_formed (by simp))
    (fun rest => call.input_field_instruction (by simp) _ rest)
    (fun rest => call.input_field_instruction (by simp) _ rest) borrowSlot resultSlot
    (access_reference_valid _ _ _ _ _ borrowWrite) (access_reference_valid _ _ _ _ _ resultWrite) post
  exact vector128_indexed_borrow segment (binaryArguments left right output ++ extra)
    frame memory _ _ c borrowHome resultHome call.1.1 incoming borrowRead borrowWrite resultWrite disjoint post continuation

#print axioms vector128_borrow_segment_checked

end UInt256Proof.Subtract.Safety
