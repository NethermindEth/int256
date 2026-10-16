import UInt256.Arithmetic.Carry
import CIL.Safety.WordLocals
import CIL.Safety.StepComposition
import CIL.Safety.WordFootprint
import CIL.Safety.AccessBelow
import CIL.Safety.ReturnMemory
import CIL.Safety.ExecutionStaticWorld
import UInt256.Safety.CallerSetup
import UInt256.Safety.LimbAccess
import UInt256.Methods.Add.SafetyResult
import UInt256.Methods.Reporting.Arithmetic
namespace UInt256Proof.Add.CarrySafety
def carryBody (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := false, locals := [.i64 0, .i64 0], localKinds := [.word64, .word64], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .arg 1,
  .add,
  .setLocal 0,
  .local 0,
  .arg 2,
  .load64,
  .add,
  .setLocal 1,
  .arg 2,
  .local 0,
  .arg 0,
  .ltu,
  .convI8,
  .local 1,
  .local 0,
  .ltu,
  .convI8,
  .add,
  .store64,
  .arg 3,
  .local 1,
  .store64,
  .ret] }
end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety

def carryWord (a b c : BitVec 64) : BitVec 64 :=
  ((if a + b < a then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64) +
  ((if a + b + c < a + b then BitVec.ofNat 32 1 else BitVec.ofNat 32 0).signExtend 64)

/-- Symbolic execution of the carry body with explicit checked memory transitions. -/
theorem carry_run_of_memory_steps (found : program[index]? = some (carryBody profile)) (a b c : BitVec 64) (carry output first second : Reference)
    (frame : Frame) (m0 m1 m2 m3 m4 : Memory)
    (locals : frame.locals = [.bytes .word64 first, .bytes .word64 second])
    (s0 : storeLocal m0 (.bytes .word64 first) (.scalar (.i64 (a + b))) =
      .ok (.bytes .word64 first, m1))
    (s1 : storeLocal m1 (.bytes .word64 second) (.scalar (.i64 (a + b + c))) =
      .ok (.bytes .word64 second, m2))
    (r0 : loadLocal m1 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))))
    (rc : loadValue m1 (.address carry) 8 = .ok (.i64 c))
    (r1 : loadLocal m2 (.bytes .word64 first) = .ok (.scalar (.i64 (a + b))))
    (r2 : loadLocal m2 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))))
    (r3 : loadLocal m3 (.bytes .word64 second) = .ok (.scalar (.i64 (a + b + c))))
    (fc1 : form m1 carry = .ok carry) (fc2 : form m2 carry = .ok carry)
    (fo3 : form m3 output = .ok output)
    (wc : write m2 carry (numberBytes (carryWord a b c).toNat 8) 1 = .ok m3)
    (wo : write m3 output (numberBytes (a + b + c).toNat 8) 1 = .ok m4) :
    run program ((carryBody profile).code.length + 1)
      index 0
      [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
      frame [] m0 = .ok (leaveFrame frame m4, []) := by
  simp [carryWord, BitVec.toNat_add] at wc
  simp [BitVec.toNat_add] at wo
  change run program 25 index 0 _ frame [] m0 = _
  iterate 23
    apply Eq.trans
    · apply run_next found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, locals, s0, s1, r0, rc, r1, r2, r3,
          checkedValue, numericValue, formValue, fc1, fc2, fo3,
          pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary, instruction, storeValue,
          referenceAt, wc, wo, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  rw [run]
  simp [found, carryBody, step, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms carry_run_of_memory_steps

end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety

/-- Ordinary access and private locals suffice; caller references may overlap since the carry is read first. -/
theorem carry_body_succeeds (found : program[index]? = some (carryBody profile)) (a b c : BitVec 64) (carry output first second : Reference)
    (frame : Frame) (memory : Memory)
    (locals : frame.locals = [.bytes .word64 first, .bytes .word64 second])
    (distinct : first.allocation ≠ second.allocation)
    (privateFirst : carry.allocation ≠ first.allocation)
    (privateSecond : carry.allocation ≠ second.allocation)
    (firstWritable : access memory first 8 1 true = .ok ())
    (secondWritable : access memory second 8 1 true = .ok ())
    (carryReadable : read memory carry 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carry 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ()) :
    ∃ stored,
      run program ((carryBody profile).code.length + 1)
        index 0
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
        frame [] memory = .ok (leaveFrame frame stored, []) ∧
      read stored output 8 1 = .ok (numberBytes (a + b + c).toNat 8) ∧
      (WordsDisjoint carry output → read stored carry 8 1 = .ok (numberBytes (carryWord a b c).toNat 8)) ∧
      (∀ id offset, id ≠ first.allocation → id ≠ second.allocation →
        OutsideWord carry id offset → OutsideWord output id offset →
        stored.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory stored := by
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨secondAllocation, secondAccess⟩ := access_requirements secondWritable
  obtain ⟨carryAllocation, carryAccess⟩ := access_requirements carryWritable
  obtain ⟨outputAllocation, outputAccess⟩ := access_requirements outputWritable
  obtain ⟨m1, w0, s0, firstRead, firstLoad⟩ := store_local_word64 (a + b) firstWritable
  have readCarry := write_preserves_disjoint_read w0 carryReadable (Or.inl privateFirst)
  obtain ⟨m2, w1, s1, secondRead, secondLoad⟩ :=
    store_local_word64 (a + b + c) (secondAccess.after_write w0).access
  have retainedFirst := write_preserves_disjoint_read w1 firstRead (Or.inl distinct)
  have carry1 := (carryAccess.after_write w0).access
  have carry2 := ((carryAccess.after_write w0).after_write w1).access
  obtain ⟨m3, wc⟩ := write_succeeds (bytes := numberBytes (carryWord a b c).toNat 8)
    (by simpa only [length] using carry2)
  have retainedSecond := write_preserves_disjoint_read wc secondRead (Or.inl (Ne.symm privateSecond))
  have output3 := (((outputAccess.after_write w0).after_write w1).after_write wc).access
  obtain ⟨m4, wo⟩ := write_succeeds (bytes := numberBytes (a + b + c).toNat 8)
    (by simpa only [length] using output3)
  refine ⟨m4, carry_run_of_memory_steps found a b c carry output first second frame memory m1 m2 m3 m4
    locals s0 s1 firstLoad (load_word64_of_read readCarry)
    (load_local_word64_of_read retainedFirst) secondLoad
    (load_local_word64_of_read retainedSecond)
    (access_reference_valid _ _ _ _ _ carry1) (access_reference_valid _ _ _ _ _ carry2)
    (access_reference_valid _ _ _ _ _ output3) wc wo, ?_, ?_, ?_, ?_⟩
  · simpa only [length] using write_readback _ _ _ _ _ wo
  · intro disjoint
    have carryRead : read m3 carry 8 1 = .ok (numberBytes (carryWord a b c).toNat 8) := by
      simpa only [length] using write_readback _ _ _ _ _ wc
    exact write_preserves_disjoint_read wo carryRead (by simpa only [WordsDisjoint, length] using disjoint)
  · intro id offset notFirst notSecond outsideCarry outsideOutput
    rw [write_word_outside wo id offset outsideOutput,
      write_word_outside wc id offset outsideCarry,
      write_word_outside w1 id offset (Or.inl notSecond),
      write_word_outside w0 id offset (Or.inl notFirst)]

  · exact (write_preserves_access_below w0 memory.nextIdentity).trans
      ((write_preserves_access_below w1 memory.nextIdentity).trans
        ((write_preserves_access_below wc memory.nextIdentity).trans
          (write_preserves_access_below wo memory.nextIdentity)))

#print axioms carry_body_succeeds

end UInt256Proof.Add.CarrySafety


namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety

/-- The carry helper's two word homes are fresh, writable and private; setup keeps caller memory. -/
theorem carry_frame_setup (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ first second frame result,
      enterFrame (carryBody profile) args memory = .ok (frame, result) ∧
      frame.locals = [.bytes .word64 first, .bytes .word64 second] ∧
      frame.owned = [first.allocation, second.allocation] ∧
      first.allocation ≠ second.allocation ∧
      read result first 8 1 = .ok (numberBytes 0 8) ∧
      read result second 8 1 = .ok (numberBytes 0 8) ∧
      access result first 8 1 true = .ok () ∧
      access result second 8 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨first, middle, madeFirst, readFirst, writeFirst, _⟩ :=
    make_local_word64 memory memory.nextIdentity (BitVec.ofNat 64 0) wellFormed
  have wfMiddle := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed madeFirst
  obtain ⟨second, result, madeSecond, readSecond, writeSecond, preserved⟩ :=
    make_local_word64 middle memory.nextIdentity (BitVec.ofNat 64 0) wfMiddle
  have freshFirst := (makeLocal_fresh _ _ _ _ _ _ _ madeFirst).2 first.allocation (by simp)
  have freshSecond := (makeLocal_fresh _ _ _ _ _ _ _ madeSecond).2 second.allocation (by simp)
  let frame : Frame := ⟨memory.nextIdentity, [.bytes .word64 first, .bytes .word64 second],
    [first.allocation, second.allocation], []⟩
  have entered : enterFrame (carryBody profile) args memory = .ok (frame, result) := by
    simp [enterFrame, carryBody, makeLocals, madeFirst, madeSecond, makeArgumentHomes, makeParameterHomes,
      frame, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨first, second, frame, result, entered, rfl, rfl, ?_, ?_, readSecond, ?_, writeSecond,
    enterFrame_preserves_caller_memory _ _ _ _ _ entered⟩
  · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le freshFirst.2 freshSecond.1)
  · rw [preserved.read first freshFirst.2 8 1]
    exact readFirst
  · rw [preserved.access first freshFirst.2 8 1 true]
    exact writeFirst

#print axioms carry_frame_setup

end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety

/-- Total checked invocation from caller permissions, including setup and teardown. -/
theorem carry_invoke_succeeds (found : program[index]? = some (carryBody profile)) (a b c : BitVec 64) (carry output : Reference) (memory : Memory)
    (wellFormed : memory.WellFormed)
    (carryReadable : read memory carry 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carry 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ()) :
    ∃ fuel result,
      invoke program fuel index
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
        memory = .ok (result, []) ∧
      loadValue result (.address output) 8 = .ok (.i64 (a + b + c)) ∧
      (WordsDisjoint carry output → loadValue result (.address carry) 8 = .ok (.i64 (carryWord a b c))) ∧
      (∀ id offset, id < memory.nextIdentity → OutsideWord carry id offset → OutsideWord output id offset →
        result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 8 1 = .ok (numberBytes (a + b + c).toNat 8) ∧
      (WordsDisjoint carry output → read result carry 8 1 = .ok (numberBytes (carryWord a b c).toNat 8)) := by
  let args := [Value.scalar (.i64 a), .scalar (.i64 b), .reference (.address carry), .reference (.address output)]
  have fc := access_reference_valid _ _ _ _ _ carryWritable
  have fo := access_reference_valid _ _ _ _ _ outputWritable
  obtain ⟨ca, cp, _, _⟩ := formed_reference_live _ _ _ fc
  obtain ⟨oa, op, _, _⟩ := formed_reference_live _ _ _ fo
  have carryOld := (wellFormed.1 _ _ cp).1
  have outputOld := (wellFormed.1 _ _ op).1
  obtain ⟨first, second, frame, enteredMemory, entered, locals, owned, distinct,
    _, _, firstWritable, secondWritable, preserved⟩ := carry_frame_setup (profile := profile) memory args wellFormed
  have fresh := enterFrame_fresh _ _ _ _ _ entered
  have firstNew := (fresh.2 first.allocation (by rw [owned]; simp)).1
  have secondNew := (fresh.2 second.allocation (by rw [owned]; simp)).1
  have readCarry : read enteredMemory carry 8 1 = .ok (numberBytes c.toNat 8) := by
    rw [preserved.read carry carryOld 8 1]; exact carryReadable
  have writeCarry : access enteredMemory carry 8 1 true = .ok () := by
    rw [preserved.access carry carryOld 8 1 true]; exact carryWritable
  have writeOutput : access enteredMemory output 8 1 true = .ok () := by
    rw [preserved.access output outputOld 8 1 true]; exact outputWritable
  obtain ⟨stored, executed, outputRead, carryRead, footprint, retainedAccess⟩ := carry_body_succeeds found a b c carry output first second
    frame enteredMemory locals distinct (Nat.ne_of_lt (Nat.lt_of_lt_of_le carryOld firstNew))
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le carryOld secondNew))
    firstWritable secondWritable readCarry writeCarry writeOutput
  have returned := leaveFrame_preserves_memory_below frame stored memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  have outputRead' : read (leaveFrame frame stored) output 8 1 = .ok (numberBytes (a + b + c).toNat 8) := by
    rw [returned.read output outputOld 8 1]; exact outputRead
  refine ⟨(carryBody profile).code.length + 1, leaveFrame frame stored, ?_,
    load_word64_of_read outputRead', ?_, ?_, ?_, outputRead', ?_⟩
  · have checked : args.mapM (checkedValue memory) = .ok args := by
      simp [args, checkedValue, numericValue, formValue, fc, fo, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    change invoke program _ index args memory = _
    simpa only [invoke, found, checked, entered, Except.mapError, Bind.bind, Except.bind] using executed

  · intro disjoint
    apply load_word64_of_read
    rw [returned.read carry carryOld 8 1]
    exact carryRead disjoint
  · intro id offset old outsideCarry outsideOutput
    rw [returned.cells id old offset,
      footprint id offset (Nat.ne_of_lt (Nat.lt_of_lt_of_le old firstNew))
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le old secondNew)) outsideCarry outsideOutput,
      preserved.cells id old offset]

  · exact preserved.accessBelow.trans
      ((retainedAccess.weaken fresh.1.next).trans returned.accessBelow)

  · intro disjoint
    rw [returned.read carry carryOld 8 1]
    exact carryRead disjoint

#print axioms carry_invoke_succeeds

end UInt256Proof.Add.CarrySafety


namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

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

#print axioms carryWord_correct
#print axioms carryWord_arithmetic

end UInt256Proof.Add.CarrySafety


namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

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
  staticWorld : StaticWorldValid (programStaticDescriptors program) before →
    StaticWorldValid (programStaticDescriptors program) after

theorem CarryPost.output_load {a b c : BitVec 64} {carryRef output : Reference} {before after : Memory}
    (post : CarryPost (program := program) a b c carryRef output before after) :
    loadValue after (.address output) 8 = .ok (.i64 (a + b + c)) := load_word64_of_read post.outputBytes

theorem CarryPost.carry_load {a b c : BitVec 64} {carryRef output : Reference} {before after : Memory}
    (post : CarryPost (program := program) a b c carryRef output before after) :
    loadValue after (.address carryRef) 8 = .ok (.i64 (UInt256Proof.carry a b c)) := load_word64_of_read post.carryBytes

/-- Simultaneous carry/result readback requires nonoverlapping output words. -/
theorem carry_checked_contract (found : program[index]? = some (carryBody profile)) (a b c : BitVec 64) (carryRef output : Reference) (memory : Memory)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (carryReadable : read memory carryRef 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carryRef 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryRef output) :
    ∃ fuel result,
      invoke program fuel index
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carryRef), .reference (.address output)]
        memory = .ok (result, []) ∧ CarryPost (program := program) a b c carryRef output memory result := by
  obtain ⟨fuel, result, invoked, _, _, footprint, retainedAccess, outputBytes, carryBytes⟩ :=
    carry_invoke_succeeds found a b c carryRef output memory wellFormed carryReadable carryWritable outputWritable
  have carryBytes := carryBytes disjoint
  rw [carryWord_correct a b c incoming] at carryBytes
  exact ⟨fuel, result, invoked,
    ⟨invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked,
      outputBytes, carryBytes, UInt256Proof.carry_bound a b c incoming,
      UInt256Proof.carry_word_nat a b c incoming, footprint, retainedAccess,
      fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩⟩

#print axioms CarryPost.output_load
#print axioms CarryPost.carry_load
#print axioms carry_checked_contract

end UInt256Proof.Add.CarrySafety


namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}

open CIL.Safety UInt256Model.Safety

/-- A carry call writing private homes preserves caller input snapshots. -/
theorem CarryPost.private_input_bytes {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost (program := program) a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions program before inputs outputs)
    {reference : Reference} (member : reference ∈ inputs)
    (notCarry : reference.allocation ≠ carryRef.allocation)
    (notOutput : reference.allocation ≠ output.allocation) :
    (fun offset => (after.cells reference.allocation offset).bits) =
      (fun offset => (before.cells reference.allocation offset).bits) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  have old := (call.1.1.1 _ _ present).1
  funext offset
  rw [post.footprint _ _ old (Or.inl notCarry) (Or.inl notOutput)]

/-- Caller authority, readable inputs and static data survive a private carry call. -/
theorem CarryPost.private_calling_conditions {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost (program := program) a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ carryRef.allocation ∧ reference.allocation ≠ output.allocation) :
    CallingConditions program after inputs outputs := by
  refine ⟨⟨post.wellFormed, ?_, ?_⟩, post.staticWorld call.2⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed inputMember)
    have old := (call.1.1.1 _ _ present).1
    obtain ⟨notCarry, notOutput⟩ := separate reference inputMember
    refine ⟨_, post.access.read_eq (call.input_snapshot inputMember) old ?_⟩
    intro i _
    exact post.footprint _ _ old (Or.inl notCarry) (Or.inl notOutput)
  · intro view member
    have writable := call.1.2.2 view member
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
    exact post.access.access writable (call.1.1.1 _ _ present).1

theorem CarryPost.private_input_field {a b c : BitVec 64} {carryRef output : Reference}
    {before after : CIL.Safety.Memory} (post : CarryPost (program := program) a b c carryRef output before after)
    {inputs outputs : List Reference}
    (call : CallingConditions program before inputs outputs)
    (separate : ∀ reference ∈ inputs,
      reference.allocation ≠ carryRef.allocation ∧ reference.allocation ≠ output.allocation)
    {reference : Reference} (member : reference ∈ inputs) (index : Fin 4) (rest : List Value) :
    instruction (.fieldAt (8 * index.val) 8) (.reference (.address reference) :: rest) after =
      .ok (after, .scalar (.i64 (inputLimb before reference index)) :: rest) := by
  rw [(post.private_calling_conditions call separate).input_field_instruction member index rest]
  simp only [inputLimb, post.private_input_bytes call member (separate reference member).1
    (separate reference member).2]

#print axioms CarryPost.private_input_bytes
#print axioms CarryPost.private_calling_conditions
#print axioms CarryPost.private_input_field

end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
variable {profile : CIL.FeatureProfile} {program : CIL.Program} {index : Nat}
open CIL.Safety UInt256Model.Safety

/-- Mathematical carry recurrence over the four initial operand limbs. -/
def scalarCarryValue (memory : CIL.Safety.Memory) (left right : Reference) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => if h : n < 4 then
      UInt256Proof.carry (inputLimb memory left ⟨n, h⟩) (inputLimb memory right ⟨n, h⟩)
        (scalarCarryValue memory left right n)
    else 0

structure ScalarCarryState (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference) (done : Nat) (carryIndex : Nat := 2) (resultBase : Nat := 3) : Prop where
  call : CallingConditions program current [left, right] [output]
  inputBytes : ∀ reference ∈ [left, right],
    (fun offset => (current.cells reference.allocation offset).bits) =
      (fun offset => (original.cells reference.allocation offset).bits)
  carrySlot : frame.locals[carryIndex]? = some (.bytes .word64 carryHome)
  resultSlots : ∀ i, frame.locals[i.val + resultBase]? = some (.bytes .word64 (results i))
  carryWrite : access current carryHome 8 1 true = .ok ()
  resultWrites : ∀ i, access current (results i) 8 1 true = .ok ()
  carryRead : read current carryHome 8 1 = .ok (numberBytes (scalarCarryValue original left right done).toNat 8)
  carryBound : (scalarCarryValue original left right done).toNat ≤ 1
  callerSeparate : ∀ reference ∈ [left, right],
    reference.allocation ≠ carryHome.allocation ∧ ∀ i, reference.allocation ≠ (results i).allocation
  carrySeparate : ∀ i, (results i).allocation ≠ carryHome.allocation
  resultSeparate : ∀ i j, i ≠ j → (results i).allocation ≠ (results j).allocation
  carryFresh : original.nextIdentity ≤ carryHome.allocation
  resultsFresh : ∀ i, original.nextIdentity ≤ (results i).allocation
  callerCells : ∀ id, id < original.nextIdentity → ∀ offset,
    current.cells id offset = original.cells id offset
  completed : ∀ i, i.val < done → read current (results i) 8 1 =
    .ok (numberBytes (inputLimb original left i + inputLimb original right i +
      scalarCarryValue original left right i.val).toNat 8)

/-- A checked carry call advances the parent invariant, keeping inputs and completed words. -/
theorem ScalarCarryState.advance {original before after : CIL.Safety.Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} {carryIndex resultBase : Nat} (index : Fin 4)
    (state : ScalarCarryState (program := program) original before frame left right output carryHome results index.val carryIndex resultBase)
    (math : CarryPost (program := program) (inputLimb original left index) (inputLimb original right index)
      (scalarCarryValue original left right index.val) carryHome (results index) before after) :
    ScalarCarryState (program := program) original after frame left right output carryHome results (index.val + 1) carryIndex resultBase := by
  have separate : ∀ reference ∈ [left, right],
      reference.allocation ≠ carryHome.allocation ∧ reference.allocation ≠ (results index).allocation :=
    fun reference member => ⟨(state.callerSeparate reference member).1,
      (state.callerSeparate reference member).2 index⟩
  have carryOld : carryHome.allocation < before.nextIdentity := by
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ state.carryWrite
    exact (state.call.1.1.1 _ _ present).1
  have resultOld : ∀ i, (results i).allocation < before.nextIdentity := by
    intro i
    obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ (state.resultWrites i)
    exact (state.call.1.1.1 _ _ present).1
  refine ⟨math.private_calling_conditions state.call separate, ?_, state.carrySlot, state.resultSlots,
    math.access.access state.carryWrite carryOld,
    fun i => math.access.access (state.resultWrites i) (resultOld i), ?_, ?_,
    state.callerSeparate, state.carrySeparate, state.resultSeparate,
    state.carryFresh, state.resultsFresh, ?_, ?_⟩
  · intro reference member
    exact (math.private_input_bytes state.call member (separate reference member).1
      (separate reference member).2).trans (state.inputBytes reference member)
  · simpa only [scalarCarryValue, dite_eq_left index.isLt] using math.carryBytes
  · simpa only [scalarCarryValue, dite_eq_left index.isLt] using math.carryBound
  · intro id old offset
    have belowCarry := Nat.lt_of_lt_of_le old state.carryFresh
    have belowResult := Nat.lt_of_lt_of_le old (state.resultsFresh index)
    exact (math.footprint id offset (Nat.lt_trans belowCarry carryOld)
      (Or.inl (Nat.ne_of_lt belowCarry)) (Or.inl (Nat.ne_of_lt belowResult))).trans
      (state.callerCells id old offset)
  · intro i done
    by_cases same : i = index
    · subst i
      exact math.outputBytes
    · have earlier : i.val < index.val := by
        have different : i.val ≠ index.val := fun h => same (Fin.ext h)
        omega
      apply math.access.read_eq (state.completed i earlier) (resultOld i)
      intro offset _
      exact math.footprint _ _ (resultOld i) (Or.inl (state.carrySeparate i))
        (Or.inl (state.resultSeparate i index same))

#print axioms ScalarCarryState.advance

end UInt256Proof.Add.CarrySafety

namespace UInt256Proof.Add.CarrySafety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

def scalarOverflowFlag (carry : BitVec 64) : BitVec 32 :=
  if BitVec.ofNat 64 0 < carry then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

def scalarSumWord (memory : CIL.Safety.Memory) (left right : Reference) (i : Fin 4) : BitVec 64 :=
  inputLimb memory left i + inputLimb memory right i + scalarCarryValue memory left right i.val

def scalarSumValue (memory : CIL.Safety.Memory) (left right : Reference) : BitVec 256 :=
  let w := scalarSumWord memory left right
  BitVec.ofNat 256 ((w 0).toNat + (w 1).toNat * 2^64 + (w 2).toNat * 2^128 + (w 3).toNat * 2^192)

theorem scalar_sum_words (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarSumWord memory left right = UInt256Proof.sumWords (inputLimb memory left) (inputLimb memory right) := by
  funext i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [scalarSumWord, scalarCarryValue, UInt256Proof.sumWords]

/-- The four ripple words equal the independent 256-bit sum of the initial operands. -/
theorem scalar_sum_value (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarSumValue memory left right = inputValue memory left + inputValue memory right := by
  change UInt256Model.value (scalarSumWord memory left right) = _
  rw [scalar_sum_words, UInt256Proof.sumWords_sum]
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [leftValue, rightValue]

theorem scalar_flag_overflow (memory : CIL.Safety.Memory) (left right : Reference) :
    scalarOverflowFlag (scalarCarryValue memory left right 4) = addOverflow memory left right := by
  have same : scalarCarryValue memory left right 4 =
      UInt256Proof.Reporting.finalCarry (inputLimb memory left) (inputLimb memory right) := rfl
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  have overflow := UInt256Proof.Reporting.finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  simp only [BitVec.ofNat_eq_ofNat, leftValue, rightValue] at overflow
  simp only [scalarOverflowFlag, same, UInt256Proof.Reporting.word_positive,
    overflow, addOverflow, BitVec.ofNat_eq_ofNat]

#print axioms scalar_sum_words
#print axioms scalar_sum_value
#print axioms scalar_flag_overflow
end UInt256Proof.Add.CarrySafety
