import UInt256.Methods.Subtract.BorrowCaller
import UInt256.Methods.Subtract.ScalarSafetySetup

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

def scalarBorrowCalls : List Nat := scalarBody.code.zipIdx.filterMap fun (op, pc) =>
  match op with
  | .call callee _ => if callee == Extracted.subtractWithBorrowIndex then some pc else none
  | _ => none

def scalarBorrowCall (index : Nat) : Nat := scalarBorrowCalls[index]?.getD 0

theorem scalar_indexed_borrow (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (borrowHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ()) (disjoint : WordsDisjoint borrowHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, BorrowPost a b c borrowHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall index.val + 1) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall index.val) args frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have fb := access_reference_valid _ _ _ _ _ borrowWrite
  have fr := access_reference_valid _ _ _ _ _ resultWrite
  apply run_borrow_call a b c borrowHome resultHome post (body := scalarBody)
    (op := .call Extracted.subtractWithBorrowIndex 4)
  · rfl
  · obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  · simp [step, checkedValue, numericValue, formValue, fb, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact wellFormed
  · exact incoming
  · exact borrowRead
  · exact borrowWrite
  · exact resultWrite
  · exact disjoint
  · exact continuation

theorem scalar_borrow_segment_checked (segment : Fin 3) (left right output : Reference)
    (frame : Frame) (memory : Memory) (c : BitVec 64) (borrowHome resultHome : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (borrowSlot : frame.locals[1]? = some (.bytes .word64 borrowHome))
    (resultSlot : frame.locals[segment.val + 3]? = some (.bytes .word64 resultHome))
    (incoming : c.toNat ≤ 1) (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ()) (disjoint : WordsDisjoint borrowHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      BorrowPost (inputLimb memory left ⟨segment.val + 1, by omega⟩)
        (inputLimb memory right ⟨segment.val + 1, by omega⟩) c borrowHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall (segment.val + 1) + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall segment.val + 1)
        (binaryArguments left right output) frame [] memory = .ok (result, returned) ∧ post result returned := by
  have tail := scalar_indexed_borrow ⟨segment.val + 1, by omega⟩ (binaryArguments left right output) frame memory
    (inputLimb memory left ⟨segment.val + 1, by omega⟩) (inputLimb memory right ⟨segment.val + 1, by omega⟩)
    c borrowHome resultHome call.1.1 incoming borrowRead borrowWrite resultWrite disjoint post continuation
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fb := access_reference_valid _ _ _ _ _ borrowWrite
  have fo := access_reference_valid _ _ _ _ _ resultWrite
  have leftRead := call.input_field_instruction (by simp : left ∈ [left, right]) ⟨segment.val + 1, by omega⟩
  have rightRead := call.input_field_instruction (by simp : right ∈ [left, right]) ⟨segment.val + 1, by omega⟩
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp at resultSlot leftRead rightRead tail
    conv in (scalarBorrowCall _) => cbv
    repeat' first
      | exact tail
      | (simp (config := { failIfUnchanged := false })
         apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, binaryArguments, checkedValue, formValue, fl, fr, fb, fo, borrowSlot, resultSlot,
             localAddress, leftRead, rightRead, checkedAt, Except.mapError, Bind.bind, Except.bind,
             Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms scalar_indexed_borrow
#print axioms scalar_borrow_segment_checked
end UInt256Proof.Subtract.Safety
