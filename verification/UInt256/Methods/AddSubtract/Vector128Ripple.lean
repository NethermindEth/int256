import CIL.Safety.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import CIL.Safety.MethodContract
import CIL.Safety.CallComposition
import UInt256.Methods.AddSubtract.Vector128Inputs
import UInt256.Methods.AddSubtract.RippleState

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

/-- The numeric local every ripple word occupies. -/
def rippleWordSpec : NumericLocalSpec := ⟨.word64, .i64 0, 0, rfl⟩

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

/-- Push the output reference and the four completed result words for the storage call. -/
theorem ripple_store_prefix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (helper storage base home : Nat) (code : CodeAt body base (rippleCode helper storage home))
    (output : Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (frame : Frame) (memory : Memory) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (snapshots : LocalSnapshots memory frame.locals (completedLocals words (home + 2) 4))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + 36) args frame
        [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 31) args frame [] memory = .ok (result, returned) ∧
        post result returned := by
  have loading (i : Fin 4) (pc : Nat) (stack : List Value) := snapshots.load
    (body := body) (args := args) (pc := pc) (stack := stack) (index := home + 2 + i.val)
    (.i64 (words i)) (by simp [completedLocals, i.isLt])
  cil_contract_steps [found, code, outputArg, outputFormed,
    loading 0, loading 1, loading 2, loading 3] until continuation

/-- Return the final flag word as an unsigned flag and retire the frame. -/
theorem ripple_return (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body)
    (helper storage base home : Nat) (code : CodeAt body base (rippleCode helper storage home))
    (returns : body.returnsValue = true)
    (args : List Value) (frame : Frame) (memory : Memory)
    (flagHome : Reference) (flagWord : BitVec 64)
    (slot : frame.locals[home + 1]? = some (.bytes .word64 flagHome))
    (loaded : read memory flagHome 8 1 = .ok (numberBytes flagWord.toNat 8)) :
    run program 5 method (base + 37) args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (rippleFlag flagWord))]) := by
  have reading := load_local_word64_of_read loaded
  iterate 4
    apply Eq.trans
    · apply run_next found (by cil_lookup [code])
      simp (config := { implicitDefEqProofs := false })
        [step, cil_guard, observerCount, slot, reading, checkedValue, numericValue, pureArity,
          scalars, CIL.step.eq_def, CIL.binary, CIL.unary, instruction, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  have fetched : body.code[base + 41]? = some (.ret (some .unsigned8)) := by
    cil_lookup [code]
  by_cases positive : BitVec.ofNat 64 0 < flagWord
  all_goals simp [run, found, fetched, returns, step, cil_guard, observerCount, checkedValue,
    numericValue, CIL.NarrowKind.extend, rippleFlag, positive, Except.mapError, Bind.bind,
    Except.bind, Pure.pure, Except.pure]

end UInt256Proof.AddSubtract.Safety
