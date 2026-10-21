import UInt256.Safety.StepEquation
import UInt256.Methods.Multiply.Calls
namespace UInt256Proof.Multiply
open CIL.Safety


def hardwareWordTail (operation : CIL.Intrinsic) : List CIL.Op :=
  [.arg 2, .arg 0, .arg 1, .mul, .store64, .arg 0, .arg 1, .intrinsic operation 2, .ret]

theorem hardware_word_tail (program : CIL.Program) (index start : Nat) (body : CIL.Method)
    (found : program[index]? = some body) (returns : body.returnsValue = true)
    (operation : CIL.Intrinsic) (available : operation.available body.profile = true)
    (code : ∀ i : Fin 9, body.code[start + i.val]? = (hardwareWordTail operation)[i.val]?)
    (evaluation : ∀ a b, checkedIntrinsic operation [.i64 a, .i64 b] = .ok (.i64 (highProduct a b)))
    (memory : Memory) (a b : BitVec 64) (output : Reference)
    (wf : memory.WellFormed) (writable : access memory output 8 1 true = .ok ()) :
    ∃ final,
      run program 9 index start [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
        ⟨memory.nextIdentity, [], [], []⟩ [] memory = .ok (final, [.scalar (.i64 (highProduct a b))]) ∧
      final.WellFormed ∧ read final output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow memory.nextIdentity memory final ∧
      (∀ id offset, id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
        final.cells id offset = memory.cells id offset) := by
  let args : List Value := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have formed := access_reference_valid _ _ _ _ _ writable
  have length : (numberBytes (lowProduct a b).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨final, written⟩ := write_succeeds (bytes := numberBytes (lowProduct a b).toNat 8)
    (by simpa only [length] using writable)
  have loaded := write_readback _ _ _ _ _ written
  rw [length] at loaded
  refine ⟨final, ?_, write_preserves_wellFormed _ _ _ _ _ wf written, loaded,
    write_preserves_access_below written _, ?_⟩
  · change run program 9 index start args frame [] memory = _
    iterate 4
      apply Eq.trans
      · apply run_next found
        · first
          | simpa [hardwareWordTail, Nat.add_assoc] using code ⟨0, by decide⟩
          | simpa [hardwareWordTail, Nat.add_assoc] using code ⟨1, by decide⟩
          | simpa [hardwareWordTail, Nat.add_assoc] using code ⟨2, by decide⟩
          | simpa [hardwareWordTail, Nat.add_assoc] using code ⟨3, by decide⟩
        · first
          | rfl
          | (simp [step, args, checkedValue, formValue, formed, checkedAt,
                Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
             try exact ⟨rfl, rfl, rfl, rfl⟩
             done)
    apply Eq.trans
    · apply run_next (target := start + 5) (values := []) (nextFrame := frame) (updated := final) found
        (by simpa [hardwareWordTail, Nat.add_assoc] using code ⟨4, by decide⟩)
      have written' : write memory output (numberBytes (a.toNat * b.toNat % 2^64) 8) 1 = .ok final := by
        simpa only [lowProduct, BitVec.toNat_mul] using written
      simp [step, pureArity, instruction, storeValue, referenceAt, ordinaryAccessAlignment, written', checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.add_assoc]
    · iterate 2
        apply Eq.trans
        · apply run_next found
          · first
            | simpa [hardwareWordTail, Nat.add_assoc] using code ⟨5, by decide⟩
            | simpa [hardwareWordTail, Nat.add_assoc] using code ⟨6, by decide⟩
          · rfl
      apply Eq.trans
      · apply run_next (target := start + 8) (values := [.scalar (.i64 (highProduct a b))])
          (nextFrame := frame) (updated := final) found
          (by simpa [hardwareWordTail, Nat.add_assoc] using code ⟨7, by decide⟩)
        simp [step, available, scalars, evaluation, checkedValue, numericValue,
          Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.add_assoc]
      · have last : body.code[start + 8]? = some .ret := by simpa [hardwareWordTail] using code ⟨8, by decide⟩
        simp [run, found, last, step, returns, leaveFrame, frame, checkedValue, numericValue,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro id offset outside
    apply write_outside _ _ _ _ _ _ _ written
    simpa only [length] using outside
#print axioms hardware_word_tail
end UInt256Proof.Multiply
namespace UInt256Proof.Multiply
def bmiWordBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .feature .bmi2,
  .brzero 11,
  .arg 2,
  .arg 0,
  .arg 1,
  .mul,
  .store64,
  .arg 0,
  .arg 1,
  .intrinsic (.bmi2 .multiplyHigh64) 2,
  .ret,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }


def armWordBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .feature .bmi2,
  .brzero 11,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .feature .armBase64,
  .brzero 22,
  .arg 2,
  .arg 0,
  .arg 1,
  .mul,
  .store64,
  .arg 0,
  .arg 1,
  .intrinsic (.armBase64 .multiplyHigh64) 2,
  .ret,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

end UInt256Proof.Multiply
namespace UInt256Proof.Multiply
open CIL.Safety

def hardwareWordBody (arm : Bool) (profile : CIL.FeatureProfile) : CIL.Method :=
  if arm then armWordBody profile else bmiWordBody profile

def hardwareWordIntrinsic (arm : Bool) : CIL.Intrinsic :=
  if arm then .armBase64 .multiplyHigh64 else .bmi2 .multiplyHigh64

theorem hardware_word_invoke (arm : Bool) (profile : CIL.FeatureProfile)
    (bmi : profile.bmi2 = !arm) (armEnabled : arm = true → profile.armBase64 = true)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (hardwareWordBody arm profile))
    (memory : Memory) (a b : BitVec 64) (output : Reference)
    (wf : memory.WellFormed) (writable : access memory output 8 1 true = .ok ()) :
    ∃ fuel final,
      invoke program fuel index [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] memory =
        .ok (final, [.scalar (.i64 (highProduct a b))]) ∧
      final.WellFormed ∧ read final output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow memory.nextIdentity memory final ∧
      (∀ id offset, id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
        final.cells id offset = memory.cells id offset) := by
  let body := hardwareWordBody arm profile
  let operation := hardwareWordIntrinsic arm
  have returns : body.returnsValue = true := by cases arm <;> rfl
  have available : operation.available body.profile = true := by
    cases arm
    · exact bmi
    · exact armEnabled rfl
  have code : ∀ i : Fin 9, body.code[(if arm then 13 else 2) + i.val]? = (hardwareWordTail operation)[i.val]? := by
    cases arm <;> intro i
    all_goals
      have split : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
          i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
      rcases split with h | h | h | h | h | h | h | h | h
      all_goals simp only [h]; rfl
  have evaluation : ∀ a b, checkedIntrinsic operation [.i64 a, .i64 b] = .ok (.i64 (highProduct a b)) := by
    cases arm <;> intros <;> rfl
  obtain ⟨final, executed, valid, loaded, authority, outside⟩ :=
    hardware_word_tail program index (if arm then 13 else 2) body found returns operation available code evaluation memory a b output wf writable
  refine ⟨if arm then 13 else 11, final, ?_, valid, loaded, authority, outside⟩
  have formed := access_reference_valid _ _ _ _ _ writable
  apply invoke_of_run found
  · simp [checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · cases arm <;> rfl
  · let args : List Value := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
    let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
    cases arm with
    | false =>
      change run program 11 index 0 args frame [] memory = _
      apply Eq.trans
      · apply run_next (target := 1) (values := [.scalar (.i32 1)]) (nextFrame := frame) (updated := memory) found (by rfl)
        change Except.ok (FrameAction.next 1 [.scalar (.i32 (if profile.bmi2 then 1 else 0))] frame memory) = _
        simp only [bmi, Bool.not_false, ↓reduceIte]
      apply Eq.trans
      · apply run_next (target := 2) (values := []) (nextFrame := frame) (updated := memory) found (by rfl)
        rfl
      exact executed
    | true =>
      change run program 13 index 0 args frame [] memory = _
      apply Eq.trans
      · apply run_next (target := 1) (values := [.scalar (.i32 0)]) (nextFrame := frame) (updated := memory) found (by rfl)
        change Except.ok (FrameAction.next 1 [.scalar (.i32 (if profile.bmi2 then 1 else 0))] frame memory) = _
        simp only [bmi, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      apply Eq.trans
      · apply run_next (target := 11) (values := []) (nextFrame := frame) (updated := memory) found (by rfl)
        rfl
      apply Eq.trans
      · apply run_next (target := 12) (values := [.scalar (.i32 1)]) (nextFrame := frame) (updated := memory) found (by rfl)
        change Except.ok (FrameAction.next 12 [.scalar (.i32 (if profile.armBase64 then 1 else 0))] frame memory) = _
        simp only [armEnabled rfl, ↓reduceIte]
      apply Eq.trans
      · apply run_next (target := 13) (values := []) (nextFrame := frame) (updated := memory) found (by rfl)
        rfl
      exact executed
#print axioms hardware_word_invoke
end UInt256Proof.Multiply
namespace UInt256Proof.Multiply
open CIL.Safety

theorem hardware_word_contract (arm : Bool) (profile : CIL.FeatureProfile)
    (bmi : profile.bmi2 = !arm) (armEnabled : arm = true → profile.armBase64 = true)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (hardwareWordBody arm profile)) : Calls.WordContract program index := by
  intro memory a b output wf writable
  obtain ⟨fuel, final, execution, valid, loaded, authority, outside⟩ :=
    hardware_word_invoke arm profile bmi armEnabled program index found memory a b output wf writable
  exact ⟨fuel, final, execution, valid, loaded, authority, fun id _ offset bound => outside id offset bound⟩
#print axioms hardware_word_contract
end UInt256Proof.Multiply
