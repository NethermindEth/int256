import UInt256.Methods.Add.Bindings
import CIL.Safety.WordLocals
import CIL.Safety.WordFootprint
import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition
import CIL.Safety.SymbolicExecution
import UInt256.Arithmetic.Carry

namespace UInt256Proof.Safety

open CIL.Safety

/-- Independent arithmetic, actual byte readbacks, and retained caller storage. -/
structure CarryPost (a b c : BitVec 64) (carryRef output : Reference) (before after : Memory) : Prop where
  wellFormed : after.WellFormed
  outputBytes : read after output 8 1 = .ok (numberBytes (a + b + c).toNat 8)
  carryBytes : read after carryRef 8 1 = .ok (numberBytes (UInt256Proof.carry a b c).toNat 8)
  carryBound : (UInt256Proof.carry a b c).toNat ≤ 1
  arithmetic : (a + b + c).toNat + 2^64 * (UInt256Proof.carry a b c).toNat = a.toNat + b.toNat + c.toNat
  footprint : ∀ id offset, id < before.nextIdentity → OutsideWord carryRef id offset → OutsideWord output id offset →
    after.cells id offset = before.cells id offset
  access : AccessBelow before.nextIdentity before after
  staticWorld : StaticWorldValid (programStaticDescriptors Extracted.program) before →
    StaticWorldValid (programStaticDescriptors Extracted.program) after

theorem CarryPost.output_load {a b c : BitVec 64} {carryRef output : Reference} {before after : Memory}
    (post : CarryPost a b c carryRef output before after) :
    loadValue after (.address output) 8 = .ok (.i64 (a + b + c)) := load_word64_of_read post.outputBytes

theorem CarryPost.carry_load {a b c : BitVec 64} {carryRef output : Reference} {before after : Memory}
    (post : CarryPost a b c carryRef output before after) :
    loadValue after (.address carryRef) 8 = .ok (.i64 (UInt256Proof.carry a b c)) := load_word64_of_read post.carryBytes

/-- The production carry word: the sum of both overflow indicators. -/
def carryWord (a b c : BitVec 64) : BitVec 64 :=
  ((if a + b < a then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64) +
  ((if a + b + c < a + b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

theorem carryWord_correct (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    carryWord a b c = UInt256Proof.carry a b c := by
  simp only [carryWord, UInt256Proof.extend_choice]
  have h := UInt256Proof.carry_expression a b c incoming
  change ((if a + b < a then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) +
    (if a + b + c < a + b then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) = _ at h
  exact h

theorem carryWord_arithmetic (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    (a + b + c).toNat + 2^64 * (carryWord a b c).toNat = a.toNat + b.toNat + c.toNat ∧
      (carryWord a b c).toNat ≤ 1 := by
  rw [carryWord_correct a b c incoming]
  exact ⟨UInt256Proof.carry_word_nat a b c incoming, UInt256Proof.carry_bound a b c incoming⟩

/-- The parent needs only a checked carry-helper invocation; each extraction proves
    this from its own helper body. Simultaneous readback requires disjoint words. -/
def CarryHelperContract : Prop :=
  ∀ (a b c : BitVec 64) (carryRef output : Reference) (memory : Memory),
    memory.WellFormed → c.toNat ≤ 1 →
    read memory carryRef 8 1 = .ok (numberBytes c.toNat 8) →
    access memory carryRef 8 1 true = .ok () →
    access memory output 8 1 true = .ok () →
    WordsDisjoint carryRef output →
    ∃ fuel result,
      invoke Extracted.program fuel Extracted.addWithCarryIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carryRef), .reference (.address output)]
        memory = .ok (result, []) ∧ CarryPost a b c carryRef output memory result

/-- Execution of a two-local carry body whose only memory effects are, in order,
    both local stores, the carry write `cw`, and the sum write. -/
def CarryRun (cw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ (a b c : BitVec 64) (carry output first second : Reference) (frame : Frame) (m0 m1 m2 m3 m4 : Memory),
    frame.locals = [.bytes .word64 first, .bytes .word64 second] →
    storeLocal m0 (.bytes .word64 first) (.scalar (.i64 (a + b))) = .ok (.bytes .word64 first, m1) →
    storeLocal m1 (.bytes .word64 second) (.scalar (.i64 (a + b + c))) = .ok (.bytes .word64 second, m2) →
    loadLocal m1 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))) →
    loadValue m1 (.address carry) 8 = .ok (.i64 c) →
    loadLocal m2 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))) →
    loadLocal m2 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))) →
    loadLocal m3 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))) →
    form m1 carry = .ok carry → form m2 carry = .ok carry → form m3 output = .ok output →
    write m2 carry (numberBytes (cw a b c).toNat 8) 1 = .ok m3 →
    write m3 output (numberBytes (a + b + c).toNat 8) 1 = .ok m4 →
    run Extracted.program (Extracted.addWithCarryBody.code.length + 1) Extracted.addWithCarryIndex 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
      frame [] m0 = .ok (leaveFrame frame m4, [])

set_option hygiene false in
/-- Prove `CarryRun` by executing every fetched instruction, including calls to
    frameless pure helpers; `normalize` puts the carry write in evaluated form. -/
macro "carry_run_steps " "[" normalize:term,* "]" : tactic => `(tactic| (
  intro a b c carry output first second frame m0 m1 m2 m3 m4 locals s0 s1 r0 rc r1 r2 r3 fc1 fc2 fo3 wc wo
  simp [$[$normalize:term],*] at wc
  simp [BitVec.toNat_add] at wo
  simp only [cil_code]
  repeat'
    first
    | apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, locals, s0, s1, r0, rc, r1, r2, r3,
              checkedValue, numericValue, formValue, fc1, fc2, fo3,
              pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary, instruction, storeValue,
              referenceAt, wc, wo, checkedAt, Except.mapError,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          exact ⟨rfl, rfl, rfl, rfl⟩
    | apply run_call_of_invoke
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp [cil_code, step, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · cil_checked_steps
      simp only [List.append_nil, Nat.reduceAdd, leaveFrame, List.foldl_nil]
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [run, cil_code, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]))

#print axioms carryWord_correct
#print axioms carryWord_arithmetic
#print axioms CarryPost.output_load
#print axioms CarryPost.carry_load

end UInt256Proof.Safety
