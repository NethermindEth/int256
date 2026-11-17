import CIL.Safety.LocalSnapshotSteps
import CIL.StepEquations
import CIL.Safety.Equations
import CIL.Safety.MethodContract
import CIL.Safety.CallComposition
import UInt256.Methods.AddSubtract.Vector128Inputs
import UInt256.Methods.AddSubtract.RippleState
import UInt256.Methods.Multiply.LimbStorage

/-!
The scalar ripple that Add and Subtract share after their vector paths: zero a private flag
word, call a limb helper once per limb, store the four result words and return the flag.
The theorems are stated at any position and local layout and over any helper contract, so
each method instantiates them with its own carry or borrow contract.
-/

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- The ripple body: the flag word is local `home + 1` and the result words follow it. -/
def rippleCode (helper storage home : Nat) : List CIL.Op := [
  .const32 0, .convI8, .setLocal (home + 1),
  .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .localAddr (home + 1), .localAddr (home + 2), .call helper 4,
  .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .localAddr (home + 1), .localAddr (home + 3), .call helper 4,
  .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .localAddr (home + 1), .localAddr (home + 4), .call helper 4,
  .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .localAddr (home + 1), .localAddr (home + 5), .call helper 4,
  .arg 2, .local (home + 2), .local (home + 3), .local (home + 4), .local (home + 5), .call storage 5,
  .local (home + 1), .const32 0, .convI8, .gtu, .ret (some .unsigned8)]

/-- The flag a ripple returns: one when its final flag word is positive. -/
def rippleFlag (word : BitVec 64) : BitVec 32 :=
  if BitVec.ofNat 64 0 < word then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

/-- Zero the private flag word before the first helper call. -/
theorem ripple_start (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (helper storage base home : Nat) (code : CodeAt body base (rippleCode helper storage home))
    (flagSpec : specs[home]? = some rippleWordSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[home + 1]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes 0 8) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes 0 8) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method (base + 3) args frame [] after = .ok (final, returned) ∧
          post final returned) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧
        post final returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root
      slots layout currentCall enteredWF homes authority home rippleWordSpec flagSpec (.i64 0) 0 rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  cil_contract_steps 2 [found, code]
  exact run_next_exists post found (by cil_lookup [code]) (stored _ _ _) done

/-- Load both operand limbs and the two private word addresses for one helper call. -/
theorem ripple_segment (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (helper storage base home : Nat) (code : CodeAt body base (rippleCode helper storage home))
    (segment : Fin 4) (left right : Reference) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (frame : Frame) (memory : Memory) (a b : BitVec 64) (flagHome resultHome : Reference)
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right)
    (leftRead : ∀ rest, instruction (.fieldAt (8 * segment.val) 8)
      (.reference (.address left) :: rest) memory = .ok (memory, .scalar (.i64 a) :: rest))
    (rightRead : ∀ rest, instruction (.fieldAt (8 * segment.val) 8)
      (.reference (.address right) :: rest) memory = .ok (memory, .scalar (.i64 b) :: rest))
    (flagSlot : frame.locals[home + 1]? = some (.bytes .word64 flagHome))
    (resultSlot : frame.locals[home + 2 + segment.val]? = some (.bytes .word64 resultHome))
    (flagFormed : form memory flagHome = .ok flagHome)
    (resultFormed : form memory resultHome = .ok resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + 9 + 7 * segment.val) args frame
        [.reference (.address resultHome), .reference (.address flagHome), .scalar (.i64 b),
          .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 3 + 7 * segment.val) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] at leftRead rightRead resultSlot continuation ⊢
    cil_contract_steps [found, code, leftArg, rightArg, leftFormed, rightFormed,
      flagFormed, resultFormed, flagSlot, resultSlot, localAddress, leftRead, rightRead] until continuation

/-- One fetched helper call composes with the helper's checked contract. -/
theorem ripple_call {Input : Type} (contract : MethodContract Input Unit)
    (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (helper storage base home : Nat) (code : CodeAt body base (rippleCode helper storage home))
    (holds : contract.Holds program helper) (input : Input)
    (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b : BitVec 64) (flagHome resultHome : Reference)
    (encoded : contract.args input = [.scalar (.i64 a), .scalar (.i64 b),
      .reference (.address flagHome), .reference (.address resultHome)])
    (returnsNothing : ∀ output, contract.results output = [])
    (wellFormed : memory.WellFormed) (permitted : contract.pre input memory)
    (flagWrite : access memory flagHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after output, after.WellFormed →
      StaticWorldPreserved program memory after →
      Confined (contract.footprint input) memory after →
      contract.post input memory after output →
      ∃ fuel result returned,
        run program fuel method (base + 10 + 7 * index.val) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 9 + 7 * index.val) args frame
        [.reference (.address resultHome), .reference (.address flagHome), .scalar (.i64 b),
          .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have flagFormed := access_reference_valid _ _ _ _ _ flagWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  have fetched : body.code[base + 9 + 7 * index.val]? = some (.call helper 4) := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · show body.code[base + 9]? = _; cil_lookup [code]
    · show body.code[base + 16]? = _; cil_lookup [code]
    · show body.code[base + 23]? = _; cil_lookup [code]
    · show body.code[base + 30]? = _; cil_lookup [code]
  have stepped : step body (.call helper 4) (base + 9 + 7 * index.val) args frame
      [.reference (.address resultHome), .reference (.address flagHome), .scalar (.i64 b),
        .scalar (.i64 a)] memory =
      .ok (.call helper [.scalar (.i64 a), .scalar (.i64 b), .reference (.address flagHome),
        .reference (.address resultHome)] [] memory) := by
    cil_checked_step [flagFormed, resultFormed]
  apply run_call_of_contract_formed holds input found fetched stepped encoded.symm permitted
    wellFormed
  intro after output call kept
  simpa only [show base + 9 + 7 * index.val + 1 = base + 10 + 7 * index.val by omega,
    returnsNothing, List.nil_append] using
    continuation after output kept.formed kept.staticWorld call.framed call.post

/-- Caller views discharge both limb loads; the helper's contract discharges its call. -/
theorem ripple_limb {Input : Type} (contract : MethodContract Input Unit)
    (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (helper storage base home : Nat) (code : CodeAt body base (rippleCode helper storage home))
    (holds : contract.Holds program helper) (input : Input)
    (segment : Fin 4) (left right output : Reference) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (frame : Frame) (memory : Memory) (flagHome resultHome : Reference)
    (call : CallingConditions program memory [left, right] [output])
    (flagSlot : frame.locals[home + 1]? = some (.bytes .word64 flagHome))
    (resultSlot : frame.locals[home + 2 + segment.val]? = some (.bytes .word64 resultHome))
    (encoded : contract.args input = [.scalar (.i64 (inputLimb memory left segment)),
      .scalar (.i64 (inputLimb memory right segment)),
      .reference (.address flagHome), .reference (.address resultHome)])
    (returnsNothing : ∀ output, contract.results output = [])
    (permitted : contract.pre input memory)
    (flagWrite : access memory flagHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (post : Memory → List Value → Prop)
    (continuation : ∀ after output, after.WellFormed →
      StaticWorldPreserved program memory after →
      Confined (contract.footprint input) memory after →
      contract.post input memory after output →
      ∃ fuel result returned,
        run program fuel method (base + 10 + 7 * segment.val) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 3 + 7 * segment.val) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  apply ripple_segment program body method found helper storage base home code
    segment left right args leftArg rightArg frame memory _ _ flagHome resultHome
    (call.input_formed (by simp)) (call.input_formed (by simp))
    (fun rest => call.input_field_instruction (by simp) _ rest)
    (fun rest => call.input_field_instruction (by simp) _ rest) flagSlot resultSlot
    (access_reference_valid _ _ _ _ _ flagWrite) (access_reference_valid _ _ _ _ _ resultWrite) post
  exact ripple_call contract program body method found helper storage base home code holds input
    segment args frame memory _ _ flagHome resultHome encoded returnsNothing call.1.1 permitted
    flagWrite resultWrite post continuation

/-- Store completed ripple words and return the preserved private flag through checked calls. -/
theorem ripple_finish (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (helper storage base home : Nat) (code : CodeAt body base (rippleCode helper storage home))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (returns : body.returnsValue = true) (original memory : Memory) (frame : Frame)
    (left right output flagHome : Reference) (results : Fin 4 → Reference)
    (flags : Nat → BitVec 64) (words : Fin 4 → BitVec 64) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (state : RippleState program original memory frame left right output flagHome results
      flags words 4 (home + 1) (home + 2))
    (post : Memory → List Value → Prop)
    (continuation : ∀ stored, CallingConditions program stored [left, right] [output] →
      (∀ id offset, OutsideOutput output id offset →
        stored.cells id offset = memory.cells id offset) →
      inputValue stored output = UInt256Model.value words →
      post (leaveFrame frame stored) [.scalar (.i32 (rippleFlag (flags 4)))]) :
    WP (Execution (fun fuel => run program fuel method (base + 31) args frame [] memory))
      (Function.uncurry post) := by
  have formed := state.call.output_formed (by simp : output ∈ [output])
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract body.profile program storage
      storageFound memory [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) (base + 36) args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] memory =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output
        (words 0) (words 1) (words 2) (words 3)) [] memory) := by
    cil_checked_step [UInt256Proof.Multiply.LimbStorage.arguments, formed]
  obtain ⟨_, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  have distinct : flagHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.flagFresh))
  have flagRead := authority.read_eq state.flagRead (state.call.1.1.access_bound state.flagWrite)
    (fun i _ => outside _ _ (Or.inl distinct))
  have loaded := load_local_word64_of_read flagRead
  have suffix : WP (Execution (fun fuel =>
      run program fuel method (base + 37) args frame [] stored)) (Function.uncurry post) := by
    cil_contract_steps [found, code, state.flagSlot, loaded, returns]
    simpa only [Function.uncurry, CIL.NarrowKind.extend_ite_ofNat_one_zero, rippleFlag] using
      continuation stored valid outside (by simpa only [UInt256Model.value] using value)
  have called : WP (Execution (fun fuel => run program fuel method (base + 36) args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] memory))
      (Function.uncurry post) := by
    apply WP.call (helperPost := fun result => result.1 = stored ∧ result.2 = [])
      found (by cil_lookup [code]) stepped ⟨childFuel, (stored, []), invoked, rfl, rfl⟩
    rintro final values ⟨rfl, rfl⟩
    exact suffix
  cil_contract_steps (snapshots := state.snapshots)
    [found, code, outputArg, formed, completedLocals] until called

end UInt256Proof.AddSubtract.Safety
