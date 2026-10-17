import UInt256.Methods.Subtract.Vector128Entry
import UInt256.Methods.Subtract.Vector128FastAt
import UInt256.Methods.Subtract.Vector128RepairAt
import UInt256.Methods.Subtract.ScalarDispatchWith
import UInt256.Methods.Subtract.ImplGuards

namespace UInt256Proof.Subtract.Profile

/-- One inlined limb: difference into local `12 + 2i`, result into `13 + 2i`, carried borrow into local 11. -/
def inlineLimbCode (i : Nat) : List CIL.Op := [
  .arg 0, .fieldAt (8 * i) 8, .arg 1, .fieldAt (8 * i) 8, .sub, .setLocal (12 + 2 * i),
  .local (12 + 2 * i), .local 11, .sub, .setLocal (13 + 2 * i),
  .arg 0, .fieldAt (8 * i) 8, .arg 1, .fieldAt (8 * i) 8, .ltu, .convI8,
  .local (12 + 2 * i), .local 11, .ltu, .convI8, .bor, .setLocal 11]

/-- Zero the borrow, ripple four inlined limbs, store the odd locals and return the final borrow. -/
def inlineRepairCode (storage : Nat) : List CIL.Op :=
  [.const32 0, .convI8, .setLocal 11] ++ inlineLimbCode 0 ++ inlineLimbCode 1 ++ inlineLimbCode 2 ++
    inlineLimbCode 3 ++
  [.arg 2, .local 13, .local 15, .local 17, .local 19, .call storage 5,
    .local 11, .const32 0, .convI8, .gtu, .ret (some .unsigned8)]

/-- SubtractVector128 with the borrow chain inlined into nine private words. -/
def subtractInlineVectorBody (profile : CIL.FeatureProfile) (storage : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128,
      .vector128, .vector128, .vector128, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64,
      .word64],
    parameterHomes := [], staticSites := [],
    code := UInt256Proof.AddSubtract.Safety.vector128PrefixCode ++ subtractStartCode ++
      subtractIncomingCode profile.advSimd ++ subtractDecisionCodeTo 179 ++ inlineRepairCode storage ++
      subtractFastCode }

def inlineVectorSpecs : List CIL.Safety.NumericLocalSpec :=
  List.replicate 10 UInt256Proof.AddSubtract.Safety.vector128ZeroSpec ++ List.replicate 9 subtractWordSpec

theorem inline_vector_specs :
    ∀ i : Fin 10, inlineVectorSpecs[i.val]? = some UInt256Proof.AddSubtract.Safety.vector128ZeroSpec := by
  intro i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem inline_word_specs : ∀ i : Fin 9, inlineVectorSpecs[10 + i.val]? = some subtractWordSpec := by
  intro i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The inlined borrow test is the exact borrow for an incoming borrow of at most one. -/
theorem inline_borrow_expression (a b c : BitVec 64) (incoming : c.toNat ≤ 1) :
    (if a < b then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) |||
      (if a - b < c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) = UInt256Proof.borrow a b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hz : c = 0 ∨ c = 1 := by
    have hn : c.toNat = 0 ∨ c.toNat = 1 := by omega
    rcases hn with hn | hn
    · left; apply BitVec.eq_of_toNat_eq; simpa using hn
    · right; apply BitVec.eq_of_toNat_eq; simpa using hn
  by_cases hab : a < b <;> by_cases hd : a - b < c <;> rcases hz with rfl | rfl
  all_goals simp only [UInt256Proof.borrow, hab, hd, ↓reduceIte]
  all_goals simp [BitVec.lt_def, BitVec.toNat_sub] at hab hd ⊢
  all_goals omega

theorem scalar_borrow_value_bound (memory : CIL.Safety.Memory) (left right : CIL.Safety.Reference) (n : Nat) :
    (scalarBorrowValue memory left right n).toNat ≤ 1 := by
  cases n with
  | zero => simp [scalarBorrowValue]
  | succ n =>
    simp only [scalarBorrowValue]
    split
    · exact UInt256Proof.borrow_bound _ _ _
    · simp

#print axioms inline_vector_specs
#print axioms inline_word_specs
#print axioms inline_borrow_expression
#print axioms scalar_borrow_value_bound
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Slot `j` is a private word home reading back `v`. -/
def WordHeld (current : Memory) (slots : List LocalSlot) (j : Nat) (v : BitVec 64) : Prop :=
  ∃ reference, slots[j]? = some (.bytes .word64 reference) ∧ read current reference 8 1 = .ok (numberBytes v.toNat 8)

theorem WordHeld.load {current : Memory} {slots : List LocalSlot} {j : Nat} {v : BitVec 64}
    (held : WordHeld current slots j v) (body : CIL.Method) (frame : Frame) (root : LocalSlot)
    (layout : frame.locals = root :: slots) (pc : Nat) (args stack : List Value) :
    step body (.local (j + 1)) pc args frame stack current =
      .ok (.next (pc + 1) (.scalar (.i64 v) :: stack) frame current) := by
  obtain ⟨reference, slot, loaded⟩ := held
  have actual : frame.locals[j + 1]? = some (.bytes .word64 reference) := by simpa [layout] using slot
  exact step_load_numeric_local .word64 (.i64 v) _ rfl actual loaded

/-- Borrow in slot 10 and completed difference words in slots `12 + 2i`. -/
structure InlineBorrowState (program : CIL.Program) (original entered current : Memory)
    (left right output : Reference) (slots : List LocalSlot) (done : Nat) : Prop where
  call : CallingConditions program current [left, right] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  borrow : WordHeld current slots 10 (scalarBorrowValue original left right done)
  completed : ∀ i : Fin 4, i.val < done →
    WordHeld current slots (12 + 2 * i.val) (scalarDifferenceWord original left right i)

/-- Writing one private word keeps caller facts and every other word slot. -/
theorem inline_word_store (program : CIL.Program) (body : CIL.Method) (original entered current : Memory)
    (left right output : Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity inlineVectorSpecs slots)
    (authority : AccessBelow entered.nextIdentity entered current) (j : Fin 9) (v : BitVec 64) :
    ∃ after,
      CallingConditions program after [left, right] [output] ∧
      MemoryBelow original.nextIdentity original after ∧
      AccessBelow entered.nextIdentity entered after ∧
      WordHeld after slots (10 + j.val) v ∧
      (∀ k w, k ≠ 10 + j.val → WordHeld current slots k w → WordHeld after slots k w) ∧
      ∀ pc args rest, step body (.setLocal (10 + j.val + 1)) pc args frame (.scalar (.i64 v) :: rest) current =
        .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body inlineVectorSpecs original.nextIdentity entered current [left, right] [output]
      frame root slots layout currentCall enteredWF homes authority (10 + j.val) subtractWordSpec
      (inline_word_specs j) (.i64 v) v.toNat rfl
  have tailSlot : slots[10 + j.val]? = some (.bytes .word64 reference) := by
    simpa [layout, subtractWordSpec] using slot
  refine ⟨after, afterCall, preserved.trans retained, afterAuthority, ⟨reference, tailSlot, loaded⟩, ?_, stored⟩
  intro k w different held
  obtain ⟨source, sourceSlot, sourceRead⟩ := held
  refine ⟨source, sourceSlot, write_preserves_disjoint_read written sourceRead (Or.inl ?_)⟩
  rcases Nat.lt_or_gt_of_ne different with lower | higher
  · exact Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 source reference lower sourceSlot tailSlot)
  · exact Nat.ne_of_gt (homes.ordered _ _ .word64 .word64 reference source higher tailSlot sourceSlot)

/-- Operand limbs read through any memory that keeps the caller allocations. -/
theorem inline_field (program : CIL.Program) (original current : Memory) (left right output : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (reference : Reference) (member : reference ∈ [left, right]) (i : Fin 4) (rest : List Value) :
    instruction (.fieldAt (8 * i.val) 8) (.reference (.address reference) :: rest) current =
      .ok (current, .scalar (.i64 (inputLimb original reference i)) :: rest) := by
  rw [currentCall.input_field_instruction member i rest]
  simp only [inputLimb, call.input_bytes_of_memory_below preserved member]

/-- Zero the private borrow word. -/
theorem inline_repair_start (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base : Nat) (leading tail : List CIL.Op)
    (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (original entered current : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value)
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity inlineVectorSpecs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, InlineBorrowState program original entered after left right output slots 0 →
      ∃ fuel final returned,
        run program fuel method (base + 3) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨after, afterCall, afterPreserved, afterAuthority, held, _, stored⟩ :=
    inline_word_store program body original entered current left right output frame root slots layout currentCall
      preserved enteredWF homes authority 0 0
  have done := continuation after ⟨afterCall, afterPreserved, afterAuthority, held, fun i impossible => by omega⟩
  repeat' first
    | exact done
    | (apply run_next_exists post found (by seg_fetch code leadingLength)
       first
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, pureArity, scalars, CIL.step.eq_def, CIL.unary, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms WordHeld.load
#print axioms inline_word_store
#print axioms inline_field
#print axioms inline_repair_start
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- One inlined limb writes the difference word and advances the exact borrow. -/
theorem inline_repair_limb (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base : Nat) (leading tail : List CIL.Op)
    (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (original entered before : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (call : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity inlineVectorSpecs slots)
    (index : Fin 4)
    (state : InlineBorrowState program original entered before left right output slots index.val)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, InlineBorrowState program original entered after left right output slots (index.val + 1) →
      ∃ fuel final returned,
        run program fuel method (base + 3 + 22 * index.val + 22) args frame [] after = .ok (final, returned) ∧
          post final returned) :
    ∃ fuel final returned,
      run program fuel method (base + 3 + 22 * index.val) args frame [] before = .ok (final, returned) ∧
        post final returned := by
  obtain ⟨a, ha⟩ : ∃ a, a = inputLimb original left index := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = inputLimb original right index := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = scalarBorrowValue original left right index.val := ⟨_, rfl⟩
  have bound : c.toNat ≤ 1 := hc ▸ scalar_borrow_value_bound original left right index.val
  obtain ⟨m1, c1, p1, au1, tempHeld, keep1, store1⟩ := inline_word_store program body original entered before
    left right output frame root slots layout state.call state.preserved enteredWF homes state.authority
    ⟨1 + 2 * index.val, by omega⟩ (a - b)
  obtain ⟨m2, c2, p2, au2, resultHeld, keep2, store2⟩ := inline_word_store program body original entered m1
    left right output frame root slots layout c1 p1 enteredWF homes au1 ⟨2 + 2 * index.val, by omega⟩ (a - b - c)
  obtain ⟨m3, c3, p3, au3, borrowHeld, keep3, store3⟩ := inline_word_store program body original entered m2
    left right output frame root slots layout c2 p2 enteredWF homes au2 0 (UInt256Proof.borrow a b c)
  have borrow0 : WordHeld before slots 10 c := hc ▸ state.borrow
  have borrow1 := keep1 10 c (by simp <;> omega) borrow0
  have borrow2 := keep2 10 c (by simp <;> omega) borrow1
  have temp2 := keep2 _ (a - b) (by simp) tempHeld
  have final : InlineBorrowState program original entered m3 left right output slots (index.val + 1) := by
    refine ⟨c3, p3, au3, ?_, ?_⟩
    · have next : scalarBorrowValue original left right (index.val + 1) = UInt256Proof.borrow a b c := by
        rw [ha, hb, hc]
        simp only [scalarBorrowValue, index.isLt, ↓reduceDIte]
      rw [next]
      exact borrowHeld
    · intro k lower
      by_cases same : k.val = index.val
      · have equal : k = index := Fin.ext same
        subst equal
        have kept := keep3 _ _ (by simp <;> omega) resultHeld
        have slotEq : 10 + (2 + 2 * k.val) = 12 + 2 * k.val := by omega
        simp only [Fin.val_mk, slotEq] at kept
        rw [ha, hb, hc] at kept
        exact kept
      · have old := state.completed k (by omega)
        exact keep3 _ _ (by simp <;> omega) (keep2 _ _ (by simp <;> omega) (keep1 _ _ (by simp <;> omega) old))
  have done := continuation m3 final
  have lt := temp2.load body frame root layout
  have lb1 := borrow1.load body frame root layout
  have lb2 := borrow2.load body frame root layout
  have fl0 := inline_field program original before left right output call state.call state.preserved left (by simp) index
  have fr0 := inline_field program original before left right output call state.call state.preserved right (by simp) index
  have fl2 := inline_field program original m2 left right output call c2 p2 left (by simp) index
  have fr2 := inline_field program original m2 left right output call c2 p2 right (by simp) index
  have lt1 := tempHeld.load body frame root layout
  rw [← ha] at fl0 fl2
  rw [← hb] at fr0 fr2
  rw [← inline_borrow_expression a b c bound] at store3
  have leftFormed := state.call.input_formed (reference := left) (by simp)
  have rightFormed := state.call.input_formed (reference := right) (by simp)
  have leftFormed2 := c2.input_formed (reference := left) (by simp)
  have rightFormed2 := c2.input_formed (reference := right) (by simp)
  obtain ⟨i, range⟩ := index
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.add_assoc] at lt lt1 lb1 lb2
    simp only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.add_assoc] at fl0 fr0 fl2 fr2
    simp only [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Nat.add_assoc] at store1 store2 store3 done ⊢
    repeat' first
      | exact done
      | (apply run_next_exists post found (by seg_fetch code leadingLength)
         first
         | exact store1 _ _ _
         | exact store2 _ _ _
         | exact store3 _ _ _
         | exact lt _ _ _
         | exact lt1 _ _ _
         | exact lb1 _ _ _
         | exact lb2 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, checkedValue, numericValue, formValue, leftArg, rightArg, leftFormed, rightFormed,
               leftFormed2, rightFormed2, fl0, fr0, fl2, fr2, pureArity, scalars, CIL.step.eq_def, CIL.binary,
               CIL.unary, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms inline_repair_limb
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety

/-- All four inlined limbs from the zeroed borrow. -/
theorem inline_repair_limbs (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base : Nat) (leading tail : List CIL.Op)
    (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (original entered before : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (call : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity inlineVectorSpecs slots)
    (state : InlineBorrowState program original entered before left right output slots 0)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, InlineBorrowState program original entered after left right output slots 4 →
      ∃ fuel final returned,
        run program fuel method (base + 91) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (base + 3) args frame [] before = .ok (final, returned) ∧ post final returned := by
  have s0 := inline_repair_limb program body method found base leading tail leadingLength storage code original
    entered _ left right output frame root slots layout args leftArg rightArg call enteredWF homes 0 state post
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at s0
  apply s0
  intro _ first
  have s1 := inline_repair_limb program body method found base leading tail leadingLength storage code original
    entered _ left right output frame root slots layout args leftArg rightArg call enteredWF homes 1 first post
  simp only [Fin.val_one, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] at s1 ⊢
  apply s1
  intro _ second
  have s2 := inline_repair_limb program body method found base leading tail leadingLength storage code original
    entered _ left right output frame root slots layout args leftArg rightArg call enteredWF homes 2 second post
  simp only [Fin.val_two, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at s2 ⊢
  apply s2
  intro _ third
  have s3 := inline_repair_limb program body method found base leading tail leadingLength storage code original
    entered _ left right output frame root slots layout args leftArg rightArg call enteredWF homes 3 third post
  simp only [CIL.fin_val_three, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at s3 ⊢
  exact s3 continuation

theorem inline_read_present {memory : Memory} {reference : Reference} {width alignment : Nat}
    {bytes : List (BitVec 8)} (loaded : read memory reference width alignment = .ok bytes) :
    ∃ allocation, memory.allocations reference.allocation = some allocation ∧ allocation.live = true := by
  unfold CIL.Safety.read at loaded
  cases accessed : access memory reference width alignment false with
  | error fault => simp [accessed, Bind.bind, Except.bind] at loaded
  | ok unit =>
    obtain ⟨allocation, present, live, _⟩ :=
      access_within_allocation memory reference width alignment false (by cases unit; exact accessed)
    exact ⟨allocation, present, live⟩

/-- Return the final inlined borrow as the unsigned underflow flag. -/
theorem inline_store_return (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base : Nat) (leading tail : List CIL.Op)
    (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (returns : body.returnsValue = true)
    (args : List Value) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (memory : Memory) (borrowWord : BitVec 64)
    (held : WordHeld memory slots 10 borrowWord) :
    run program 5 method (base + 97) args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (scalarUnderflowFlag borrowWord))]) := by
  have reading := held.load body frame root layout
  iterate 4
    apply Eq.trans
    · apply run_next found (by seg_fetch code leadingLength)
      first
      | exact reading _ _ _
      | (simp (config := { implicitDefEqProofs := false })
          [step, checkedValue, numericValue, pureArity, scalars,
            CIL.step.eq_def, CIL.binary, CIL.unary, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : body.code[base + 97 + 1 + 1 + 1 + 1]? = some (.ret (some .unsigned8)) := by
    seg_fetch code leadingLength
  by_cases positive : BitVec.ofNat 64 0 < borrowWord
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    scalarUnderflowFlag, positive, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Store the four inlined words through the checked limb helper and return the exact borrow. -/
theorem inline_store_finish (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base : Nat) (leading tail : List CIL.Op)
    (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (returns : body.returnsValue = true)
    (original entered current : Memory) (left right output : Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (homes : NumericHomes entered original.nextIdentity inlineVectorSpecs slots)
    (state : InlineBorrowState program original entered current left right output slots 4) :
    ∃ fuel final values,
      run program fuel method (base + 91) args frame [] current = .ok (final, values) ∧
      SubtractResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => SubtractResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have l0 := (state.completed 0 (by decide)).load body frame root layout
  have l1 := (state.completed 1 (by decide)).load body frame root layout
  have l2 := (state.completed 2 (by decide)).load body frame root layout
  have l3 := (state.completed 3 (by decide)).load body frame root layout
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul, Nat.reduceAdd,
    Nat.add_zero] at l0 l1 l2 l3
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract body.profile program storage storageFound
      current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) (base + 96) args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3))
        [] current) := by
    simp [step, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  obtain ⟨borrowHome, borrowSlot, borrowRead⟩ := state.borrow
  obtain ⟨home, homeSlot, homeFresh, _, _⟩ := homes.home_at 10 subtractWordSpec (inline_word_specs 0)
  have sameHome : home = borrowHome := by
    rw [borrowSlot] at homeSlot
    simpa [subtractWordSpec] using homeSlot.symm
  subst home
  obtain ⟨borrowAllocation, borrowPresent, _⟩ := inline_read_present borrowRead
  have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
  have distinct : borrowHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld homeFresh))
  have keptBorrow := authority.read_eq borrowRead borrowOld (fun i _ => outside _ _ (Or.inl distinct))
  have returned := inline_store_return program body method found base leading tail leadingLength storage code
    returns args frame root slots layout stored _ ⟨borrowHome, borrowSlot, keptBorrow⟩
  obtain ⟨tailFuel, ran⟩ := run_call_exists found (by seg_fetch code leadingLength) stepped ⟨childFuel, invoked⟩
    ⟨5, returned⟩
  have pushed : ∃ fuel final values,
      run program fuel method (base + 91) args frame [] current = .ok (final, values) ∧
        final = leaveFrame frame stored ∧
        values = [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))] := by
    let post' : Memory → List Value → Prop := fun final values => final = leaveFrame frame stored ∧
      values = [.scalar (.i32 (scalarUnderflowFlag (scalarBorrowValue original left right 4)))]
    have done : ∃ fuel final values,
        run program fuel method (base + 96) args frame
          [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
            .scalar (.i64 (words 0)), .reference (.address output)] current = .ok (final, values) ∧
          post' final values := ⟨tailFuel, _, _, ran, rfl, rfl⟩
    repeat' first
      | exact done
      | (apply run_next_exists post' found (by seg_fetch code leadingLength)
         first
         | exact l0 _ _ _
         | exact l1 _ _ _
         | exact l2 _ _ _
         | exact l3 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, checkedValue, formValue, outputArg, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
               Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  obtain ⟨fuel, final, values, executed, sameFinal, sameValues⟩ := pushed
  subst sameFinal
  subst sameValues
  refine ⟨fuel, leaveFrame frame stored, _, executed, ?_⟩
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity owned
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have computed : inputValue (leaveFrame frame stored) output = scalarDifferenceValue original left right := by
      simpa only [inputValue, bytes, scalarDifferenceValue] using value
    exact computed.trans (scalar_difference_value original left right)
  · rw [scalar_flag_underflow]
    rfl
  · exact (retained.access output outputOld 32 1 true).trans
      (valid.1.2.2 (wordView output) (by simp))
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.preserved.cells id old offset))

#print axioms inline_repair_limbs
#print axioms inline_store_return
#print axioms inline_store_finish
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety CIL.Vector

theorem inline_vector_first_four : ∀ i : Fin 4, inlineVectorSpecs[i.val]? = some vector128ZeroSpec :=
  fun i => inline_vector_specs ⟨i.val, by omega⟩

/-- Both branches from entry with the borrow chain inlined: modular difference, exact underflow, caller bytes kept. -/
theorem subtract_inline_vector_entry (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractInlineVectorBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (subtractInlineVectorBody profile storage) args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity inlineVectorSpecs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output))) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let body := subtractInlineVectorBody profile storage
  let values := subtractInputValues original left right
  let saved := vector128SavedFrame frame slots right
  let decided := vector128PrefixCode ++ subtractStartCode ++ subtractIncomingCode profile.advSimd
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ saved.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  have decidedLength : decided.length = 63 := subtract_incoming_leading _
  let post := fun final returned => SubtractResult original final returned left right output
  apply vector128_inputs_checked program body method inlineVectorSpecs found
    (subtractStartCode ++ subtractIncomingCode profile.advSimd ++ subtractDecisionCodeTo 179 ++
      inlineRepairCode storage ++ subtractFastCode)
    (by simp only [body, subtractInlineVectorBody, List.append_assoc]) inline_vector_first_four
    original entered [left, right] [output] left right frame slots args call setup layout homes
    (by simp) (by simp) leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority _
  have state := subtract_initial_state program original entered current left right output slots l0 l1 r0 r1
    s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority
  apply subtract_start_checked program body method inlineVectorSpecs found vector128PrefixCode
    (subtractIncomingCode profile.advSimd ++ subtractDecisionCodeTo 179 ++ inlineRepairCode storage ++
      subtractFastCode) rfl
    (by simp only [body, subtractInlineVectorBody, List.append_assoc]) inline_vector_specs
    original entered current [left, right] [output] saved _ slots savedLayout args enteredWF homes values state post
  intro m8 s8
  apply subtract_incoming_checked program body method inlineVectorSpecs found
    (vector128PrefixCode ++ subtractStartCode)
    (subtractDecisionCodeTo 179 ++ inlineRepairCode storage ++ subtractFastCode)
    rfl (by simp only [body, subtractInlineVectorBody, List.append_assoc]) sse ssse inline_vector_specs
    original entered m8 [left, right] [output] saved _ slots savedLayout args enteredWF homes values s8 post
  intro m10 s10
  apply subtract_decision_checked_at program body method found 63 179 decided
    (inlineRepairCode storage ++ subtractFastCode)
    decidedLength (by simp only [body, decided, subtractInlineVectorBody, List.append_assoc])
    original entered m10 [left, right] [output] saved _ slots savedLayout args values s10 post
  by_cases fast : subtractPropagation values = BitVec.ofNat 128 0
  · simp only [fast, ite_true]
    obtain ⟨fuel, final, returned, executed, wellFormed, flag, lowRead, highRead, writable, footprint⟩ :=
      subtract_fast_checked_at program body method inlineVectorSpecs found 179
        (decided ++ subtractDecisionCodeTo 179 ++ inlineRepairCode storage) []
        (by simp only [List.length_append, decidedLength]; rfl)
        (by simp only [body, decided, subtractInlineVectorBody, List.append_assoc, List.append_nil]) rfl
        inline_vector_specs original entered m10 [left, right] [output] output saved _ slots savedLayout args call
        (by simp) outputArg homes values s10 owned
    exact ⟨fuel, final, returned, executed,
      subtract_fast_result original final left right output returned fast wellFormed flag lowRead highRead writable footprint⟩
  · simp only [fast, ite_false]
    have repairCode : body.code = (decided ++ subtractDecisionCodeTo 179) ++ inlineRepairCode storage ++
        subtractFastCode := by
      simp only [body, decided, subtractInlineVectorBody, List.append_assoc]
    have repairLength : (decided ++ subtractDecisionCodeTo 179).length = 77 := by
      simp only [List.length_append, decidedLength]; rfl
    apply inline_repair_start program body method found 77 _ _ repairLength storage repairCode
      original entered m10 left right output saved _ slots savedLayout args s10.call s10.preserved enteredWF homes
      s10.authority post
    intro ready readyState
    apply inline_repair_limbs program body method found 77 _ _ repairLength storage repairCode
      original entered ready left right output saved _ slots savedLayout args leftArg rightArg call enteredWF homes
      readyState post
    intro after doneState
    exact inline_store_finish program body method found 77 _ _ repairLength storage repairCode storageFound rfl
      original entered after left right output saved _ slots savedLayout args outputArg call owned homes doneState

/-- Checked invocation of the inlined-carry SubtractVector128 with its storage callee. -/
theorem checked_subtract_inline_vector (program : CIL.Program) (method storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractInlineVectorBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true) :
    VectorChecked program method := by
  intro memory left right output call
  let args := binaryArguments left right output
  obtain ⟨frame, entered, slots, setup, layout, homes, _, _⟩ :=
    vector128_frame_setup (subtractInlineVectorBody profile storage) inlineVectorSpecs ⟨rfl, rfl⟩ rfl rfl
      memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    subtract_inline_vector_entry program method storage profile found storageFound sse ssse
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

#print axioms subtract_inline_vector_entry
#print axioms checked_subtract_inline_vector
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- SubtractVector128 ripples its repair borrow through nine private words instead of a helper. -/
theorem checked_inline_carry_impl (program : CIL.Program) (impl scalar vector small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (implFound : program[impl]? = some (subtractImplBodyWith profile scalar (avx2Guard 123) 123))
    (scalarFound : program[scalar]? = some (subtractScalarBodyWith profile vector small 9 100))
    (vectorFound : program[vector]? = some (subtractInlineVectorBody profile storage))
    (smallFound : program[small]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl := by
  apply subtract_impl_contract_with program impl scalar profile _ 123 implFound
    (avx2_guard_skips program impl scalar 123 profile implFound noAvx2)
  intro memory left right output call
  obtain ⟨fuel, final, values, certified, result⟩ :=
    checked_subtract_scalar_contract_with program scalar vector small profile scalarFound
      (checked_subtract_inline_vector program vector storage profile vectorFound storageFound sse ssse)
      (small_checked_of_body program small storage profile smallFound storageFound) sse42 memory left right output call
  exact ⟨fuel, final, values, certified.1, result⟩

#print axioms checked_inline_carry_impl
end UInt256Proof.Subtract.Profile
