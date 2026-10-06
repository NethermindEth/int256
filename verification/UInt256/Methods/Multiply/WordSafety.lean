import Extracted
import UInt256.Methods.Multiply.Product
import CIL.Safety.FrameProgress
import CIL.Safety.WordMemory
import CIL.Safety.ReturnMemory
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

/-- Discover the widening helper by its mixed-width private frame. Every
    selected instruction, including the intrinsic overload, is still checked. -/
def wordIndex : Nat := Extracted.program.findIdx fun body =>
  match body.localKinds with
  | [.word32, .word32, .word32, .word64, .word64, .word64] => true
  | _ => false

def wordBody : CIL.Method := Extracted.program[wordIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def hardwareReturnPc : Nat := if Extracted.profile.bmi2 then 10 else 21

/-- SkipLocalsInit metadata is preserved: these six homes start unknown.
    The hardware paths never read them. -/
theorem word_frame_setup (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered, enterFrame wordBody args memory = .ok (frame, entered) := by
  apply enterFrame_succeeds wordBody args memory wf
  have kinds : wordBody.localKinds = [.word32, .word32, .word32, .word64, .word64, .word64] := by rfl
  have locals : wordBody.locals = [.unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled] := by rfl
  have arguments : wordBody.aggregateArgs = [] := by rfl
  simp [FrameSetupFits, kinds, locals, arguments, InitializersFit, InitializerFits, AggregateArgumentsFit]

/-- Both widening-intrinsic paths write the exact low product and return the
    exact high product. The output needs write authority, not prior initialization. -/
theorem hardware_word_invoke (memory : Memory) (a b : BitVec 64) (output : Reference)
    (wf : memory.WellFormed) (writable : access memory output 8 1 true = .ok ())
    (hardware : Extracted.profile.bmi2 = true ∨ Extracted.profile.armBase64 = true) :
    ∃ fuel final,
      invoke Extracted.program fuel wordIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] memory =
        .ok (final, [.scalar (.i64 (highProduct a b))]) ∧
      final.WellFormed ∧
      read final output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow memory.nextIdentity memory final ∧
      (∀ id, id < memory.nextIdentity → ∀ offset,
        id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
        final.cells id offset = memory.cells id offset) := by
  first
  | exact False.elim ((by decide : ¬ (Extracted.profile.bmi2 = true ∨ Extracted.profile.armBase64 = true)) hardware)
  |
    let args := [Value.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
    have formed := access_reference_valid _ _ _ _ _ writable
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ formed
    have old := (wf.1 _ _ present).1
    obtain ⟨frame, entered, setup⟩ := word_frame_setup memory args wf
    have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
    have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ wf setup
    have ready : access entered output 8 1 true = .ok () :=
      (before.access output old 8 1 true).trans writable
    have enteredFormed := access_reference_valid _ _ _ _ _ ready
    have length : (numberBytes (lowProduct a b).toNat 8).length = 8 := by simp [numberBytes]
    obtain ⟨stored, written⟩ := write_succeeds (bytes := numberBytes (lowProduct a b).toNat 8)
      (by simpa only [length] using ready)
    have loaded := write_readback _ _ _ _ _ written
    rw [length] at loaded
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have after := leaveFrame_preserves_memory_below frame stored memory.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨24, leaveFrame frame stored, ?_,
      leaveFrame_preserves_wellFormed _ _ (write_preserves_wellFormed _ _ _ _ _ enteredWF written),
      (after.read output old 8 1).trans loaded,
      before.accessBelow.trans ((write_preserves_access_below written _).trans after.accessBelow), ?_⟩
    · have found : Extracted.program[wordIndex]? = some wordBody := by rfl
      have profile : wordBody.profile = Extracted.profile := by rfl
      have normalizedWrite : write entered output (numberBytes (a.toNat * b.toNat % 2^64) 8) 1 = .ok stored := by
        simpa only [lowProduct, BitVec.toNat_mul] using written
      have checked : args.mapM (checkedValue memory) = .ok args := by
        simp [args, checkedValue, numericValue, formValue, formed, checkedAt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      have terminal (fuel : Nat) : run Extracted.program (fuel + 1) wordIndex hardwareReturnPc args frame
          [.scalar (.i64 (highProduct a b))] stored =
          .ok (leaveFrame frame stored, [.scalar (.i64 (highProduct a b))]) := by
        have fetched : wordBody.code[hardwareReturnPc]? = some .ret := by rfl
        rw [run]
        simp only [found, fetched]
        rfl
      change invoke Extracted.program 24 wordIndex args memory = _
      simp only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
      conv in wordIndex => cbv
      repeat'
        first
        | exact terminal _
        | try simp (config := { implicitDefEqProofs := false }) [profile, Extracted.profile, CIL.FeatureProfile.evaluate]
          apply Eq.trans
          · apply run_next (body := wordBody)
            · exact found
            · rfl
            · first
              | rfl
              | simp (config := { implicitDefEqProofs := false })
                  [step, args, checkedValue, numericValue, formValue, enteredFormed, checkedAt,
                    pureArity, instruction, storeValue, referenceAt, normalizedWrite,
                    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
                first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · intro id bound offset outside
      rw [after.cells id bound offset]
      exact (write_outside _ _ _ _ _ id offset written (by simpa only [length] using outside)).trans
        (before.cells id bound offset)

#print axioms word_frame_setup
#print axioms hardware_word_invoke
end UInt256Proof.Multiply.Safety
