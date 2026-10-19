import UInt256.Methods.Subtract.Vector128Entry
import UInt256.Methods.Subtract.Vector128FastAt
import UInt256.Methods.Subtract.Vector128RepairAt
import UInt256.Methods.Subtract.ScalarDispatchWith
import UInt256.Methods.Subtract.ImplGuards

namespace UInt256Proof.Subtract.Profile

/-- Save the right root and three input halves; the upper left half stays on the stack. -/
def lanePrefixCode : List CIL.Op := [
  .arg 0, .memory .asRef, .memory .asRef, .arg 1, .memory .asRef, .memory .asRef, .setLocal 0,
  .local 0, .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 1,
  .dup, .memory .load128, .setLocal 2,
  .local 0, .memory .load128, .setLocal 3,
  .const32 1, .memory (.add 16 true), .memory .load128]

/-- Lane differences and borrow masks into locals 4 to 7, consuming the stacked upper left half. -/
def laneStartCode : List CIL.Op := [
  .local 2, .local 3, .intrinsic (.vector (.sub64 128)) 2, .setLocal 4,
  .dup, .local 1, .intrinsic (.vector (.sub64 128)) 2, .setLocal 5,
  .local 2, .local 3, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 6,
  .local 1, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 7]

def laneIncomingCode (adv : Bool) : List CIL.Op := if adv then [
  .feature .advSimd, .brzero 49,
  .intrinsic (.vector (.zero 128)) 0, .local 6, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 8,
  .local 6, .local 7, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 9,
  .branch 61,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile"
] else [
  .feature .advSimd, .brzero 49,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 6, .const32 8, .intrinsic (.sse .shiftLeftBytes) 2, .setLocal 8,
  .local 7, .intrinsic (.vector (.reinterpret 128)) 1, .local 6, .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8, .intrinsic (.sse .alignBytes) 3, .intrinsic (.vector (.reinterpret 128)) 1, .setLocal 9]

theorem lane_incoming_length (adv : Bool) : (laneIncomingCode adv).length = 25 := by
  cases adv <;> rfl

def laneDecisionCode : List CIL.Op := [
  .local 4, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 8, .intrinsic (.vector (.band 128)) 2,
  .local 5, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 9, .intrinsic (.vector (.band 128)) 2,
  .intrinsic (.vector (.bor 128)) 2,
  .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero 117]

def laneFastCode : List CIL.Op := [
  .arg 2, .skipInit, .arg 2, .memory .asRef, .dup,
  .local 4, .local 8, .intrinsic (.vector (.add64 128)) 2, .memory .store128,
  .const32 1, .memory (.add 16 true),
  .local 5, .local 9, .intrinsic (.vector (.add64 128)) 2, .memory .store128,
  .local 7, .const32 1, .intrinsic (.vector (.extract64 128)) 2,
  .const32 0, .convI8, .gtu, .ret (some .unsigned8)]

/-- SubtractVector128 keeping one fewer vector local: snapshot `i >= 4` lives in local `i`. -/
def subtractLaneVectorBody (profile : CIL.FeatureProfile) (borrow storage : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128,
      .vector128, .vector128, .word64, .word64, .word64, .word64, .word64],
    parameterHomes := [], staticSites := [],
    code := lanePrefixCode ++ laneStartCode ++ laneIncomingCode profile.advSimd ++ laneDecisionCode ++
      subtractRepairBorrowCode 10 borrow ++ subtractStoreCode 10 storage ++ laneFastCode }

def laneVectorSpecs : List CIL.Safety.NumericLocalSpec :=
  List.replicate 9 UInt256Proof.AddSubtract.Safety.vector128ZeroSpec ++ List.replicate 5 subtractWordSpec

theorem lane_vector_specs :
    ∀ i : Fin 9, laneVectorSpecs[i.val]? = some UInt256Proof.AddSubtract.Safety.vector128ZeroSpec := by
  intro i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem lane_word_specs : ∀ i : Fin 5, laneVectorSpecs[9 + i.val]? = some subtractWordSpec := by
  intro i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The slot holding each snapshot; the upper left half (snapshot 1) is never saved. -/
def laneSlot : Nat → Nat
  | 0 => 1
  | 2 => 2
  | 3 => 0
  | n => n - 1

#print axioms lane_vector_specs
#print axioms lane_word_specs
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Slot `j` is a private vector home reading back `v`. -/
def VectorHeld (current : Memory) (slots : List LocalSlot) (j : Nat) (v : BitVec 128) : Prop :=
  ∃ reference, slots[j]? = some (.bytes .vector128 reference) ∧
    read current reference 16 1 = .ok (numberBytes v.toNat 16)

theorem VectorHeld.load {current : Memory} {slots : List LocalSlot} {j : Nat} {v : BitVec 128}
    (held : VectorHeld current slots j v) (body : CIL.Method) (frame : Frame) (root : LocalSlot)
    (layout : frame.locals = root :: slots) (pc : Nat) (args stack : List Value) :
    step body (.local (j + 1)) pc args frame stack current =
      .ok (.next (pc + 1) (.scalar (.v128 v) :: stack) frame current) := by
  obtain ⟨reference, slot, loaded⟩ := held
  have actual : frame.locals[j + 1]? = some (.bytes .vector128 reference) := by simpa [layout] using slot
  exact step_load_numeric_local .vector128 (.v128 v) _ rfl actual loaded

/-- Snapshots 0, 2 and 3 from the prefix, then every later one below `done`, each in its lane slot. -/
structure LaneState (program : CIL.Program) (original entered current : Memory)
    (left right output : Reference) (slots : List LocalSlot) (values : Fin 4 → BitVec 128) (done : Nat) : Prop where
  call : CallingConditions program current [left, right] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  held : ∀ i : Fin 10, i.val ≠ 1 → i.val < done → VectorHeld current slots (laneSlot i.val) (subtractSnapshot values i)

theorem lane_slot_bound (i : Fin 10) (skip : i.val ≠ 1) : laneSlot i.val < 9 := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by
    simp only at skip
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [laneSlot]

/-- Held snapshots below `done` sit in slots below `done - 1`. -/
theorem lane_slot_before (i : Fin 10) (skip : i.val ≠ 1) (done : Nat) (lower : i.val < done) (start : 4 ≤ done) :
    laneSlot i.val < done - 1 := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i := by
    simp only at skip
    omega
  rcases cases with rfl | rfl | rfl | large
  · simp [laneSlot]; omega
  · simp [laneSlot]; omega
  · simp [laneSlot]; omega
  · have shape : laneSlot i = i - 1 := by
      match i, large with
      | n + 4, _ => rfl
    simp only at lower
    rw [shape]
    omega

/-- Storing snapshot `done` into local `done` keeps every earlier snapshot and all caller facts. -/
theorem LaneState.store {program : CIL.Program} {original entered current : Memory}
    {left right output : Reference} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (state : LaneState program original entered current left right output slots values done)
    (body : CIL.Method) (frame : Frame) (root : LocalSlot) (layout : frame.locals = root :: slots)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity laneVectorSpecs slots)
    (start : 4 ≤ done) (bound : done < 10) :
    ∃ after, LaneState program original entered after left right output slots values (done + 1) ∧
      ∀ pc args rest, step body (.setLocal done) pc args frame
        (.scalar (.v128 (subtractSnapshot values ⟨done, bound⟩)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  have specified : laneVectorSpecs[done - 1]? = some vector128ZeroSpec :=
    lane_vector_specs ⟨done - 1, by omega⟩
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body laneVectorSpecs original.nextIdentity entered current [left, right] [output]
      frame root slots layout state.call enteredWF homes state.authority (done - 1) vector128ZeroSpec specified
      (.v128 (subtractSnapshot values ⟨done, bound⟩)) (subtractSnapshot values ⟨done, bound⟩).toNat rfl
  have tailSlot : slots[done - 1]? = some (.bytes .vector128 reference) := by
    simpa [layout, vector128ZeroSpec] using slot
  have index : done - 1 + 1 = done := by omega
  rw [index] at stored
  refine ⟨after, ⟨afterCall, state.preserved.trans retained, afterAuthority, ?_⟩, stored⟩
  intro i skip lower
  by_cases same : i.val = done
  · have equal : i = ⟨done, bound⟩ := Fin.ext same
    subst equal
    have shape : laneSlot done = done - 1 := by
      match done, start with
      | n + 4, _ => rfl
    rw [shape]
    exact ⟨reference, tailSlot, loaded⟩
  · obtain ⟨source, sourceSlot, sourceRead⟩ := state.held i skip (by omega)
    have before := lane_slot_before i skip done (by omega) start
    exact ⟨source, sourceSlot, vector128_prior_read laneVectorSpecs entered current after original.nextIdentity slots
      homes _ _ before source reference sourceSlot tailSlot _ _ written sourceRead⟩

theorem LaneState.load {program : CIL.Program} {original entered current : Memory}
    {left right output : Reference} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (state : LaneState program original entered current left right output slots values done)
    (frame : Frame) (root : LocalSlot) (layout : frame.locals = root :: slots)
    (i : Fin 10) (skip : i.val ≠ 1) (lower : i.val < done) (body : CIL.Method) (pc : Nat) (args stack : List Value) :
    step body (.local (laneSlot i.val + 1)) pc args frame stack current =
      .ok (.next (pc + 1) (.scalar (.v128 (subtractSnapshot values i)) :: stack) frame current) :=
  (state.held i skip lower).load body frame root layout pc args stack

theorem LaneState.transfer {program : CIL.Program} {original entered before after : Memory}
    {left right output : Reference} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (state : LaneState program original entered before left right output slots values done)
    (homes : NumericHomes entered original.nextIdentity laneVectorSpecs slots)
    (kept : ∀ reference, original.nextIdentity ≤ reference.allocation → ∀ bytes,
      read before reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes)
    (i : Fin 10) (skip : i.val ≠ 1) (lower : i.val < done) :
    VectorHeld after slots (laneSlot i.val) (subtractSnapshot values i) := by
  obtain ⟨reference, slot, loaded⟩ := state.held i skip lower
  obtain ⟨home, homeSlot, fresh, _, _⟩ :=
    homes.home_at (laneSlot i.val) vector128ZeroSpec (lane_vector_specs ⟨_, lane_slot_bound i skip⟩)
  have same : home = reference := by
    rw [slot] at homeSlot
    simpa [vector128ZeroSpec] using homeSlot.symm
  subst home
  exact ⟨reference, slot, kept reference fresh _ loaded⟩

theorem LaneState.retain {program : CIL.Program} {original entered current : Memory}
    {left right output : Reference} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (state : LaneState program original entered current left right output slots values done)
    (fewer : Nat) (smaller : fewer ≤ done) :
    LaneState program original entered current left right output slots values fewer :=
  ⟨state.call, state.preserved, state.authority, fun i skip lower => state.held i skip (by omega)⟩

#print axioms VectorHeld.load
#print axioms lane_slot_before
#print axioms LaneState.store
#print axioms LaneState.load
#print axioms LaneState.transfer
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Save the right root and three initial input halves; the upper left half is left on the stack. -/
theorem lane_prefix_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanePrefixCode ++ tail)
    (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity laneVectorSpecs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      LaneState program original entered after left right output slots (subtractInputValues original left right) 4 →
      ∃ fuel result returned,
        run program fuel method 21 args (vector128SavedFrame frame slots right)
          [.scalar (.v128 (inputHalf original left 1))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered = .ok (result, returned) ∧ post result returned := by
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have authority : AccessBelow entered.nextIdentity entered entered := (MemoryBelow.refl _ _).accessBelow
  have enteredWF := enteredCall.1.1
  let saved := vector128SavedFrame frame slots right
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have savedRoot : saved.locals[0]? = some (.root (some (.address right))) := rfl
  obtain ⟨h0, m1, slot0, read0, retained0, c1, a1, w0, st0⟩ :=
    vector128_local_store program body laneVectorSpecs original.nextIdentity entered entered [left, right] [output]
      saved _ slots savedLayout enteredCall enteredWF homes authority 0 vector128ZeroSpec (lane_vector_specs 0)
      (.v128 (inputHalf original right 1)) _ rfl
  have p1 := preserved.trans retained0
  obtain ⟨h1, m2, slot1, read1, retained1, c2, a2, w1, st1⟩ :=
    vector128_local_store program body laneVectorSpecs original.nextIdentity entered m1 [left, right] [output]
      saved _ slots savedLayout c1 enteredWF homes a1 1 vector128ZeroSpec (lane_vector_specs 1)
      (.v128 (inputHalf original left 0)) _ rfl
  have p2 := p1.trans retained1
  obtain ⟨h2, m3, slot2, read2, retained2, c3, a3, w2, st2⟩ :=
    vector128_local_store program body laneVectorSpecs original.nextIdentity entered m2 [left, right] [output]
      saved _ slots savedLayout c2 enteredWF homes a2 2 vector128ZeroSpec (lane_vector_specs 2)
      (.v128 (inputHalf original right 0)) _ rfl
  have p3 := p2.trans retained2
  have tail0 : slots[0]? = some (.bytes .vector128 h0) := by simpa [savedLayout, vector128ZeroSpec] using slot0
  have tail1 : slots[1]? = some (.bytes .vector128 h1) := by simpa [savedLayout, vector128ZeroSpec] using slot1
  have tail2 : slots[2]? = some (.bytes .vector128 h2) := by simpa [savedLayout, vector128ZeroSpec] using slot2
  have kept0 := vector128_prior_read laneVectorSpecs entered m2 m3 original.nextIdentity slots homes 0 2 (by decide)
    h0 h2 tail0 tail2 _ _ w2
    (vector128_prior_read laneVectorSpecs entered m1 m2 original.nextIdentity slots homes 0 1 (by decide)
      h0 h1 tail0 tail1 _ _ w1 read0)
  have kept1 := vector128_prior_read laneVectorSpecs entered m2 m3 original.nextIdentity slots homes 1 2 (by decide)
    h1 h2 tail1 tail2 _ _ w2 read1
  obtain ⟨v0, v1, v2, v3⟩ := subtract_input_values original left right
  have state : LaneState program original entered m3 left right output slots (subtractInputValues original left right) 4 := by
    refine ⟨c3, p3, a3, ?_⟩
    intro i skip lower
    obtain ⟨i, bound⟩ := i
    have cases : i = 0 ∨ i = 2 ∨ i = 3 := by
      simp only at skip lower
      omega
    rcases cases with rfl | rfl | rfl
    · refine ⟨h1, tail1, ?_⟩
      change read m3 h1 16 1 = .ok (numberBytes (subtractInputValues original left right 0).toNat 16)
      rw [v0]
      exact kept1
    · refine ⟨h2, tail2, ?_⟩
      change read m3 h2 16 1 = .ok (numberBytes (subtractInputValues original left right 2).toNat 16)
      rw [v2]
      exact read2
    · refine ⟨h0, tail0, ?_⟩
      change read m3 h0 16 1 = .ok (numberBytes (subtractInputValues original left right 3).toNat 16)
      rw [v3]
      exact kept0
  have done := continuation m3 state
  have rRight1 := vector128_input_load program original entered [left, right] [output] right 1 call enteredCall
    (by simp) preserved
  have rLeft0 := vector128_input_load program original m1 [left, right] [output] left 0 call c1 (by simp) p1
  have rRight0 := vector128_input_load program original m2 [left, right] [output] right 0 call c2 (by simp) p2
  have rLeft1 := vector128_input_load program original m3 [left, right] [output] left 1 call c3 (by simp) p3
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at rRight1 rLeft0 rRight0 rLeft1
  have advRight := enteredCall.input_half_address (by simp : right ∈ [left, right]) 1
  have advLeft := c3.input_half_address (by simp : left ∈ [left, right]) 1
  simp only [Fin.val_one, Nat.mul_one] at advRight advLeft
  have leftFormed := enteredCall.input_formed (reference := left) (by simp)
  have rightFormed := enteredCall.input_formed (reference := right) (by simp)
  have rightFormed2 := c2.input_formed (reference := right) (by simp)
  repeat' first
    | exact done
    | (apply run_next_exists post found (by simp [code, lanePrefixCode]; rfl)
       first
       | exact st0 _ _ _
       | exact st1 _ _ _
       | exact st2 _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, leftArg, rightArg, checkedValue, formValue, leftFormed, rightFormed, rightFormed2,
             staticInstruction, memoryInstruction, storeLocal, layout, vector128SavedFrame, savedRoot, loadLocal,
             CIL.offsetValue, referenceAt, advRight, advLeft, rRight1, rLeft0, rRight0, rLeft1,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms lane_prefix_checked
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- Lane differences and borrow masks from the saved halves and the stacked upper left half. -/
theorem lane_start_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 21)
    (code : body.code = leading ++ laneStartCode ++ tail)
    (original entered current : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity laneVectorSpecs slots) (values : Fin 4 → BitVec 128)
    (state : LaneState program original entered current left right output slots values 4)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, LaneState program original entered after left right output slots values 8 →
      ∃ fuel result returned,
        run program fuel method 36 args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 21 args frame [.scalar (.v128 (values 1))] current = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨m4, s5, st4⟩ := state.store body frame root layout enteredWF homes (by decide) (by decide)
  obtain ⟨m5, s6, st5⟩ := s5.store body frame root layout enteredWF homes (by decide) (by decide)
  obtain ⟨m6, s7, st6⟩ := s6.store body frame root layout enteredWF homes (by decide) (by decide)
  obtain ⟨m7, s8, st7⟩ := s7.store body frame root layout enteredWF homes (by decide) (by decide)
  have done := continuation m7 s8
  have a0 := state.load frame root layout 0 (by decide) (by decide) body
  have a2 := state.load frame root layout 2 (by decide) (by decide) body
  have b3 := s5.load frame root layout 3 (by decide) (by decide) body
  have c0 := s6.load frame root layout 0 (by decide) (by decide) body
  have c2 := s6.load frame root layout 2 (by decide) (by decide) body
  have d3 := s7.load frame root layout 3 (by decide) (by decide) body
  have e0 : subtractSnapshot values 0 = values 0 := rfl
  have e2 : subtractSnapshot values 2 = values 2 := rfl
  have e3 : subtractSnapshot values 3 = values 3 := rfl
  have e4 : subtractSnapshot values ⟨4, by decide⟩ = zip128 (· - ·) (values 0) (values 2) := rfl
  have e5 : subtractSnapshot values ⟨5, by decide⟩ = zip128 (· - ·) (values 1) (values 3) := rfl
  have e6 : subtractSnapshot values ⟨6, by decide⟩ =
      zip128 (fun x y => mask64 (x.ult y)) (values 0) (values 2) := rfl
  have e7 : subtractSnapshot values ⟨7, by decide⟩ =
      zip128 (fun x y => mask64 (x.ult y)) (values 1) (values 3) := rfl
  rw [e0] at a0 c0
  rw [e2] at a2 c2
  rw [e3] at b3 d3
  rw [e4] at st4
  rw [e5] at st5
  rw [e6] at st6
  rw [e7] at st7
  repeat' first
    | exact done
    | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, laneStartCode]; rfl)
       first
       | exact a0 _ _ _
       | exact a2 _ _ _
       | exact b3 _ _ _
       | exact c0 _ _ _
       | exact c2 _ _ _
       | exact d3 _ _ _
       | exact st4 _ _ _
       | exact st5 _ _ _
       | exact st6 _ _ _
       | exact st7 _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_sub128, CIL.Vector.intrinsic_lt128, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- The selected ISA's incoming-borrow instructions store both shifted masks in locals 8 and 9. -/
theorem lane_incoming_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 36)
    (code : body.code = leading ++ laneIncomingCode body.profile.advSimd ++ tail)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (original entered current : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity laneVectorSpecs slots) (values : Fin 4 → BitVec 128)
    (state : LaneState program original entered current left right output slots values 8)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, LaneState program original entered after left right output slots values 10 →
      ∃ fuel result returned,
        run program fuel method 61 args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 36 args frame [] current = .ok (result, returned) ∧ post result returned := by
  obtain ⟨m8, s9, st8⟩ := state.store body frame root layout enteredWF homes (by decide) (by decide)
  obtain ⟨m9, s10, st9⟩ := s9.store body frame root layout enteredWF homes (by decide) (by decide)
  have done := continuation m9 s10
  have a6 := state.load frame root layout 6 (by decide) (by decide) body
  have b6 := s9.load frame root layout 6 (by decide) (by decide) body
  have b7 := s9.load frame root layout 7 (by decide) (by decide) body
  have e6 : subtractSnapshot values 6 = subtractMask (values 0) (values 2) := rfl
  have e7 : subtractSnapshot values 7 = subtractMask (values 1) (values 3) := rfl
  have e8 : subtractSnapshot values ⟨8, by decide⟩ = incoming128Low (subtractMask (values 0) (values 2)) := rfl
  have e9 : subtractSnapshot values ⟨9, by decide⟩ =
      incoming128High (subtractMask (values 0) (values 2)) (subtractMask (values 1) (values 3)) := rfl
  rw [e6] at a6 b6
  rw [e7] at b7
  rw [e8] at st8
  rw [e9] at st9
  cases selected : body.profile.advSimd
  · rw [← incoming128_sse_low] at st8
    rw [← incoming128_sse_high] at st9
    repeat' first
      | exact done
      | (apply run_next_exists post found
           (by simp [code, List.getElem?_append, leadingLength, laneIncomingCode, selected]; rfl)
         first
         | exact a6 _ _ _
         | exact b6 _ _ _
         | exact b7 _ _ _
         | exact st8 _ _ _
         | exact st9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [show (BitVec.setWidth 8 (8 : BitVec 32)).toNat = 8 from rfl, step, selected, sse, ssse, pureArity,
               scalars, CIL.step.eq_def, CIL.Intrinsic.available, CIL.FeatureProfile.evaluate,
               CIL.Vector.intrinsic_sse_shift, CIL.Vector.intrinsic_sse_align,
               CIL.Vector.intrinsic_reinterpret128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  · rw [← incoming128_arm_low] at st8
    rw [← incoming128_arm_high] at st9
    repeat' first
      | exact done
      | (apply run_next_exists post found
           (by simp [code, List.getElem?_append, leadingLength, laneIncomingCode, selected]; rfl)
         first
         | exact a6 _ _ _
         | exact b6 _ _ _
         | exact b7 _ _ _
         | exact st8 _ _ _
         | exact st9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, selected, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available, CIL.FeatureProfile.evaluate,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_adv_extract, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Branch on the actual coalesced propagation test without writing memory. -/
theorem lane_decision_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 61)
    (code : body.code = leading ++ laneDecisionCode ++ tail)
    (original entered current : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (values : Fin 4 → BitVec 128)
    (state : LaneState program original entered current left right output slots values 10)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if subtractPropagation values = BitVec.ofNat 128 0 then 117 else 75) args frame []
        current = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 61 args frame [] current = .ok (result, returned) ∧ post result returned := by
  have a4 := state.load frame root layout 4 (by decide) (by decide) body
  have a5 := state.load frame root layout 5 (by decide) (by decide) body
  have a8 := state.load frame root layout 8 (by decide) (by decide) body
  have a9 := state.load frame root layout 9 (by decide) (by decide) body
  by_cases zero : subtractPropagation values = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    unfold subtractPropagation at zero
    iterate 14
      apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, laneDecisionCode]; rfl)
      first
      | exact a4 _ _ _
      | exact a5 _ _ _
      | exact a8 _ _ _
      | exact a9 _ _ _
      | (simp (config := { implicitDefEqProofs := false })
           [CIL.truth, Option.bind, List.mapM, checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def,
             CIL.Intrinsic.available, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128,
             CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_equal_all128,
             show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    try simp only [List.reverse_nil]
    split
    all_goals first
      | exact continuation
      | (exfalso; simp only [show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl] at *; simp_all)

#print axioms lane_start_checked
#print axioms lane_incoming_checked
#print axioms lane_decision_checked
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- The fast suffix returns the saved top-lane borrow mask from local 7 and retires its frame. -/
theorem lane_fast_return_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (code : body.code = leading ++ laneFastCode ++ tail) (returns : body.returnsValue = true)
    (memory : Memory) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (values : Fin 4 → BitVec 128)
    (held : VectorHeld memory slots (laneSlot 7) (subtractSnapshot values 7)) :
    run program 7 method (base + 15) args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0 then 1 else 0))]) := by
  have load := held.load body frame root layout
  iterate 6
    apply Eq.trans
    · apply run_next found (by seg_fetch code leadingLength)
      first
      | exact load _ _ _
      | (simp (config := { implicitDefEqProofs := false })
          [checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def, CIL.binary,
            CIL.Intrinsic.available, CIL.Vector.intrinsic_extract128,
            checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : body.code[base + 15 + 1 + 1 + 1 + 1 + 1 + 1]? = some (.ret (some .unsigned8)) := by
    seg_fetch code leadingLength
  by_cases borrow : lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend, borrow,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Store the speculative halves from the lane locals and return the top borrow. -/
theorem lane_fast_checked_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (code : body.code = leading ++ laneFastCode ++ tail) (returns : body.returnsValue = true)
    (original entered current : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (argument : args[2]? = some (.reference (.address output)))
    (homes : NumericHomes entered original.nextIdentity laneVectorSpecs slots)
    (values : Fin 4 → BitVec 128)
    (state : LaneState program original entered current left right output slots values 10)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧
      final.WellFormed ∧
      returned = [.scalar (.i32 (if lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
      read final output 16 1 =
        .ok (numberBytes (zip128 (· + ·) (subtractSnapshot values 4) (subtractSnapshot values 8)).toNat 16) ∧
      read final { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (zip128 (· + ·) (subtractSnapshot values 5) (subtractSnapshot values 9)).toNat 16) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  have member : output ∈ [output] := by simp
  obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
      afterAuthority, outside, privateReads, _⟩ :=
    output_halves_update program original entered current [left, right] [output] output
      (zip128 (· + ·) (subtractSnapshot values 4) (subtractSnapshot values 8))
      (zip128 (· + ·) (subtractSnapshot values 5) (subtractSnapshot values 9))
      call state.call member state.authority
  have a4 := state.load frame root layout 4 (by decide) (by decide) body
  have a8 := state.load frame root layout 8 (by decide) (by decide) body
  have b5 := (state.transfer homes (fun reference fresh bytes loaded =>
    (privateReads reference 16 1 bytes fresh loaded).1) 5 (by decide) (by decide)).load body frame root layout
  have b9 := (state.transfer homes (fun reference fresh bytes loaded =>
    (privateReads reference 16 1 bytes fresh loaded).1) 9 (by decide) (by decide)).load body frame root layout
  have afterTop := state.transfer homes (fun reference fresh bytes loaded =>
    (privateReads reference 16 1 bytes fresh loaded).2) 7 (by decide) (by decide)
  have formed := state.call.output_formed member
  have address := middleCall.output_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at address
  have returned := lane_fast_return_at program body method found base leading tail leadingLength code returns
    after frame root slots layout args values afterTop
  let post : Memory → List Value → Prop := fun final values' =>
    final = leaveFrame frame after ∧
      values' = [.scalar (.i32 (if lane64 (subtractSnapshot values 7) 1 > BitVec.ofNat 64 0 then 1 else 0))]
  have done : ∃ fuel result values', run program fuel method (base + 15) args frame [] after = .ok (result, values') ∧
      post result values' := ⟨7, _, _, returned, rfl, rfl⟩
  have executed : ∃ fuel result values', run program fuel method base args frame [] current =
      .ok (result, values') ∧ post result values' := by
    repeat' first
      | exact done
      | (apply run_next_exists post found (by seg_fetch code leadingLength)
         first
         | exact a4 _ _ _
         | exact a8 _ _ _
         | exact b5 _ _ _
         | exact b9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, step, argument, checkedValue, formValue, formed, instruction, staticInstruction,
               memoryInstruction, storeValue, referenceAt, firstWrite, secondWrite, address, CIL.offsetValue,
               checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_add128, numericValue,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  obtain ⟨fuel, final, values', run, sameFinal, sameValues⟩ := executed
  subst sameFinal
  subst sameValues
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  refine ⟨fuel, _, _, run, leaveFrame_preserves_wellFormed _ _ afterCall.1.1, rfl,
    (teardown.read output old 16 1).trans firstRead,
    (teardown.read { output with offset := output.offset + 16 } old 16 1).trans secondRead,
    (teardown.access output old 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩)), ?_⟩
  intro id offset earlier untouched
  exact (teardown.cells id earlier offset).trans ((outside id offset untouched).trans
    (state.preserved.cells id earlier offset))

#print axioms lane_fast_return_at
#print axioms lane_fast_checked_at
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety CIL.Vector

theorem lane_decision_leading (adv : Bool) :
    (lanePrefixCode ++ laneStartCode ++ laneIncomingCode adv).length = 61 := by
  rw [List.length_append, lane_incoming_length]
  rfl

/-- Both branches from entry with one fewer vector local: modular difference, exact underflow, caller bytes kept. -/
theorem subtract_lane_vector_entry (program : CIL.Program) (method borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractLaneVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (subtractLaneVectorBody profile borrow storage) args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity laneVectorSpecs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output))) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let body := subtractLaneVectorBody profile borrow storage
  let values := subtractInputValues original left right
  let saved := vector128SavedFrame frame slots right
  let decided := lanePrefixCode ++ laneStartCode ++ laneIncomingCode profile.advSimd
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ saved.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  have decidedLength : decided.length = 61 := lane_decision_leading _
  let post := fun final returned => SubtractResult original final returned left right output
  obtain ⟨_, v1, _, _⟩ := subtract_input_values original left right
  apply lane_prefix_checked program body method found
    (laneStartCode ++ laneIncomingCode profile.advSimd ++ laneDecisionCode ++
      subtractRepairBorrowCode 10 borrow ++ subtractStoreCode 10 storage ++ laneFastCode)
    (by simp only [body, subtractLaneVectorBody, List.append_assoc])
    original entered left right output frame slots args call setup layout homes leftArg rightArg post
  intro m4 s4
  rw [← v1]
  apply lane_start_checked program body method found lanePrefixCode
    (laneIncomingCode profile.advSimd ++ laneDecisionCode ++ subtractRepairBorrowCode 10 borrow ++
      subtractStoreCode 10 storage ++ laneFastCode) rfl
    (by simp only [body, subtractLaneVectorBody, List.append_assoc])
    original entered m4 left right output saved _ slots savedLayout args enteredWF homes values s4 post
  intro m8 s8
  apply lane_incoming_checked program body method found (lanePrefixCode ++ laneStartCode)
    (laneDecisionCode ++ subtractRepairBorrowCode 10 borrow ++ subtractStoreCode 10 storage ++ laneFastCode)
    rfl (by simp only [body, subtractLaneVectorBody, List.append_assoc]) sse ssse
    original entered m8 left right output saved _ slots savedLayout args enteredWF homes values s8 post
  intro m10 s10
  apply lane_decision_checked program body method found decided
    (subtractRepairBorrowCode 10 borrow ++ subtractStoreCode 10 storage ++ laneFastCode)
    decidedLength (by simp only [body, decided, subtractLaneVectorBody, List.append_assoc])
    original entered m10 left right output saved _ slots savedLayout args values s10 post
  by_cases fast : subtractPropagation values = BitVec.ofNat 128 0
  · simp only [fast, ite_true]
    obtain ⟨fuel, final, returned, executed, wellFormed, flag, lowRead, highRead, writable, footprint⟩ :=
      lane_fast_checked_at program body method found 117
        (decided ++ laneDecisionCode ++ subtractRepairBorrowCode 10 borrow ++ subtractStoreCode 10 storage) []
        (by simp only [List.length_append, decidedLength]; rfl)
        (by simp only [body, decided, subtractLaneVectorBody, List.append_assoc, List.append_nil]) rfl
        original entered m10 left right output saved _ slots savedLayout args call outputArg homes values s10 owned
    exact ⟨fuel, final, returned, executed,
      subtract_fast_result original final left right output returned fast wellFormed flag lowRead highRead writable footprint⟩
  · simp only [fast, ite_false]
    apply subtract_repair_borrow_at program body method laneVectorSpecs found 75 9
      (decided ++ laneDecisionCode)
      (subtractStoreCode 10 storage ++ laneFastCode) (by simp only [List.length_append, decidedLength]; rfl) borrow
      (by simp only [body, decided, subtractLaneVectorBody, List.append_assoc]) borrowFound lane_word_specs
      original entered m10 saved _ slots savedLayout left right output call s10.call s10.preserved homes enteredWF
      s10.authority args leftArg rightArg post
    intro borrowHome results after borrowState
    exact subtract_store_finish_at program body method found 106 10
      (decided ++ laneDecisionCode ++ subtractRepairBorrowCode 10 borrow)
      laneFastCode (by simp only [List.length_append, decidedLength]; rfl) storage
      (by simp only [body, decided, subtractLaneVectorBody, List.append_assoc]) storageFound rfl original after saved
      left right output borrowHome results args outputArg call owned borrowState

/-- Checked invocation of the lane-local SubtractVector128 with its borrow and storage callees. -/
theorem checked_subtract_lane_vector (program : CIL.Program) (method borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractLaneVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true) :
    VectorChecked program method := by
  intro memory left right output call
  let args := binaryArguments left right output
  obtain ⟨frame, entered, slots, setup, layout, homes, _, _⟩ :=
    vector128_frame_setup (subtractLaneVectorBody profile borrow storage) laneVectorSpecs ⟨rfl, rfl⟩ rfl rfl
      memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    subtract_lane_vector_entry program method borrow storage profile found borrowFound storageFound sse ssse
      memory entered left right output frame slots args call setup layout homes rfl rfl rfl
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, binaryArguments, checkedValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method _ args memory frame entered fuel final returned found checked setup live executed,
    result⟩

#print axioms subtract_lane_vector_entry
#print axioms checked_subtract_lane_vector
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- SubtractVector128 keeps one fewer vector local, holding the upper left half on the stack. -/
theorem checked_lane_locals_impl (program : CIL.Program) (impl scalar vector borrow small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (implFound : program[impl]? = some (subtractImplBodyWith profile scalar (avx2Guard 123) 123))
    (scalarFound : program[scalar]? = some (subtractScalarBodyWith profile vector small 5 41))
    (vectorFound : program[vector]? = some (subtractLaneVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (smallFound : program[small]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl := by
  apply subtract_impl_contract_with program impl scalar profile _ 123 implFound
    (avx2_guard_skips program impl scalar 123 profile implFound noAvx2)
  intro memory left right output call
  obtain ⟨fuel, final, values, certified, result⟩ :=
    checked_subtract_scalar_contract_with program scalar vector small profile scalarFound
      (checked_subtract_lane_vector program vector borrow storage profile vectorFound borrowFound storageFound sse ssse)
      (small_checked_of_body program small storage profile smallFound storageFound) sse42 memory left right output call
  exact ⟨fuel, final, values, certified.1, result⟩

#print axioms checked_lane_locals_impl
end UInt256Proof.Subtract.Profile
