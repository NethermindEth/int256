import UInt256.Methods.Multiply.Calls
import UInt256.Methods.Multiply.ProductValue
import UInt256.Methods.Multiply.ProductStorageContract
import UInt256.Safety.OutputCallReturn
import CIL.Safety.WordSnapshotPreservation

/-! Private-home transitions shared by the multiplication paths: local stores, widening and
    carry-counting helper calls over remembered words, and the final product storage call. -/

namespace UInt256Proof.Multiply.BothTwo
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls

/-- A notation for arithmetic expressions, not evidence that a local is readable.
    Every execution use separately proves `known index = some value`. -/
def localWord (known : Nat → Option (BitVec 64)) (index : Nat) : BitVec 64 := (known index).getD 0

def widenWords (known : Nat → Option (BitVec 64)) (left right target result : Nat) :=
  rememberWord (rememberWord known target (lowProduct (localWord known left) (localWord known right)))
    result (highProduct (localWord known left) (localWord known right))

def countWords (known : Nat → Option (BitVec 64)) (left right counter result : Nat) :=
  rememberWord (rememberWord known counter
    (countCarry (localWord known left) (localWord known right) (localWord known counter)))
    result (localWord known left + localWord known right)

/-- An initialized local holds exactly its `localWord`. -/
theorem localWord_remembered {known : Nat → Option (BitVec 64)} {index : Nat}
    (present : (known index).isSome = true) : known index = some (localWord known index) := by
  cases found : known index <;> simp_all [localWord]

variable {program : CIL.Program} {method pc : Nat} {body : CIL.Method}
  {args rest : List Value} {frame : Frame} {original entered current : Memory}
  {inputs outputs : List Reference} {known : Nat → Option (BitVec 64)}
  {post : Memory → List Value → Prop}

/-- A write of `value` to a private word home remembers it and keeps the caller's bytes. -/
theorem _root_.UInt256Model.Safety.PrivateWords.after_word_write {program : CIL.Program}
    {original entered current after : Memory} {inputs outputs : List Reference} {frame : Frame}
    {known : Nat → Option (BitVec 64)} {kinds : List CIL.LocalKind} {index : Nat}
    {home : Reference} {value : BitVec 64}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (homes : CompleteWritableHomes entered original.nextIdentity kinds frame.locals)
    (slot : frame.locals[index]? = some (.bytes .word64 home))
    (written : write current home (numberBytes value.toNat 8) 1 = .ok after) :
    PrivateWords program original entered after inputs outputs frame
      (rememberWord known index value) :=
  have preserved := write_preserves_memory_below _ _ _ _ _ _
    (homes.writable.home_bound index .word64 home slot) written
  ⟨state.call.after_write written, state.enteredBound,
    Nat.le_trans state.next (write_extends_allocations _ _ _ _ _ written).next,
    state.authority.trans ((write_preserves_access_below written _).weaken state.next),
    state.snapshots.after_write homes.writable state.call.1.1 index home value slot written,
    fun id old offset => (preserved.cells id old offset).trans (state.caller id old offset)⟩

/-- A write to a private vector home keeps every remembered word and the caller's bytes. -/
theorem _root_.UInt256Model.Safety.PrivateWords.after_vector_write {program : CIL.Program}
    {original entered current after : Memory} {inputs outputs : List Reference} {frame : Frame}
    {known : Nat → Option (BitVec 64)} {kinds : List CIL.LocalKind} {index : Nat}
    {home : Reference} {bytes : List (BitVec 8)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (homes : CompleteWritableHomes entered original.nextIdentity kinds frame.locals)
    (slot : frame.locals[index]? = some (.bytes .vector256 home))
    (written : write current home bytes 1 = .ok after) :
    PrivateWords program original entered after inputs outputs frame known :=
  have preserved := write_preserves_memory_below _ _ _ _ _ _
    (homes.writable.home_bound index .vector256 home slot) written
  ⟨state.call.after_write written, state.enteredBound,
    Nat.le_trans state.next (write_extends_allocations _ _ _ _ _ written).next,
    state.authority.trans ((write_preserves_access_below written _).weaken state.next),
    state.snapshots.after_other_kind_write homes.writable index .vector256 home (by decide) slot
      written,
    fun id old offset => (preserved.cells id old offset).trans (state.caller id old offset)⟩

/-- Store the top word in a private home, remembering it for the continuation. -/
theorem run_store_local {kinds : List CIL.LocalKind} {result : (Memory × List Value) → Prop}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity kinds frame.locals)
    (index : Nat) (kind : kinds[index]? = some .word64) (value : BitVec 64)
    (found : program[method]? = some body) (code : body.code[pc]? = some (.setLocal index))
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord known index value) →
      WP (Execution (fun fuel => run program fuel method (pc + 1) args frame rest after)) result) :
    WP (Execution (fun fuel => run program fuel method pc args frame
      (.scalar (.i64 value) :: rest) current)) result := by
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes index kind value pc args rest
    (body := body)
  exact WP.step found code stored (continuation after next)

/-- Widen the top word with an initialized local: the low product initializes `target` and
    the returned high product is stored in `result`. -/
theorem run_widen_operand {wordIndex : Nat} (contract : WordContract program wordIndex)
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity body.localKinds frame.locals)
    (right target result : Nat) (operand : BitVec 64)
    (rightKnown : (known right).isSome = true)
    (targetKind : body.localKinds[target]? = some .word64)
    (resultKind : body.localKinds[result]? = some .word64)
    (found : program[method]? = some body)
    (code : CodeAt body pc
      [.local right, .localAddr target, .call wordIndex 3, .setLocal result])
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord (rememberWord known target (lowProduct operand (localWord known right)))
          result (highProduct operand (localWord known right))) →
      WP (Execution (fun fuel => run program fuel method (pc + 4) args frame rest after))
        (Function.uncurry post)) :
    WP (Execution (fun fuel => run program fuel method pc args frame
      (.scalar (.i64 operand) :: rest) current)) (Function.uncurry post) := by
  obtain ⟨reference, slot, ready, formed⟩ := state.home enteredWF homes target targetKind
  apply WP.step found (code.lookup 0 rfl)
    (state.snapshots.load _ (localWord_remembered rightKnown))
  apply WP.step found (code.lookup 1 rfl) (by cil_checked_step [slot, formed, localAddress])
  apply run_word_call contract state originalCall homes target reference operand
    (localWord known right) slot ready post found (code.lookup 2 rfl)
    (by cil_checked_step [formed])
  intro middle middleState
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    run_store_local middleState enteredWF homes result resultKind _ found (code.lookup 3 rfl)
      continuation

/-- Widen two initialized locals: the low product initializes `target` and the returned
    high product is stored in `result`. -/
theorem run_widen_locals {wordIndex : Nat} (contract : WordContract program wordIndex)
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity body.localKinds frame.locals)
    (left right target result : Nat)
    (leftKnown : (known left).isSome = true) (rightKnown : (known right).isSome = true)
    (targetKind : body.localKinds[target]? = some .word64)
    (resultKind : body.localKinds[result]? = some .word64)
    (found : program[method]? = some body)
    (code : CodeAt body pc
      [.local left, .local right, .localAddr target, .call wordIndex 3, .setLocal result])
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (widenWords known left right target result) →
      WP (Execution (fun fuel => run program fuel method (pc + 5) args frame rest after))
        (Function.uncurry post)) :
    WP (Execution (fun fuel => run program fuel method pc args frame rest current))
      (Function.uncurry post) :=
  run_local_word_call state originalCall enteredWF homes left right target result _ _ _ _
    (localWord_remembered leftKnown) (localWord_remembered rightKnown) targetKind resultKind
    found (code.lookup 0 rfl) (code.lookup 1 rfl) (code.lookup 2 rfl) (code.lookup 3 rfl)
    (code.lookup 4 rfl)
    (fun reference _ ready =>
      widening_local_effect contract current _ _ state.call.1.1 reference ready)
    post continuation

/-- Add two initialized locals: the sum is stored in `result` and its carry is added to the
    initialized `counter`. -/
theorem run_count_locals {profile : CIL.FeatureProfile} {countIndex : Nat}
    (countFound : program[countIndex]? = some (CountSafety.body profile))
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity body.localKinds frame.locals)
    (left right counter result : Nat)
    (leftKnown : (known left).isSome = true) (rightKnown : (known right).isSome = true)
    (counterKnown : (known counter).isSome = true)
    (counterKind : body.localKinds[counter]? = some .word64)
    (resultKind : body.localKinds[result]? = some .word64)
    (found : program[method]? = some body)
    (code : CodeAt body pc
      [.local left, .local right, .localAddr counter, .call countIndex 3, .setLocal result])
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (countWords known left right counter result) →
      WP (Execution (fun fuel => run program fuel method (pc + 5) args frame rest after))
        (Function.uncurry post)) :
    WP (Execution (fun fuel => run program fuel method pc args frame rest current))
      (Function.uncurry post) :=
  run_local_word_call state originalCall enteredWF homes left right counter result _ _ _ _
    (localWord_remembered leftKnown) (localWord_remembered rightKnown) counterKind resultKind
    found (code.lookup 0 rfl) (code.lookup 1 rfl) (code.lookup 2 rfl) (code.lookup 3 rfl)
    (code.lookup 4 rfl)
    (counting_local_effect profile program countIndex countFound state.snapshots
      state.call.1.1 counter _ _ _ (localWord_remembered counterKnown))
    post continuation

/-- Pass four product words to the checked storage helper and return. Retiring the private
    homes leaves the caller output holding the value of `words`; other caller bytes are kept. -/
theorem run_product_storage {storageIndex : Nat} {output : Reference} {expected : BitVec 256}
    (storage : ProductStorage.Contract program storageIndex)
    (state : PrivateWords program original entered current inputs [output] frame known)
    (originalCall : CallingConditions program original inputs [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (words : UInt256Model.Limbs) (correct : UInt256Model.value words = expected)
    (found : program[method]? = some body)
    (code : CodeAt body pc [.call storageIndex 5, .ret])
    (returnsNothing : body.returnsValue = false) :
    WP (Execution (fun fuel => run program fuel method pc args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] current))
      (fun result => OutputResult original result.1 output expected result.2) := by
  have formed := state.call.output_formed (by simp : output ∈ [output])
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    storage current inputs output (words 0) (words 1) (words 2) (words 3) state.call
  have packed : inputValue result output = UInt256Model.value words := value
  exact WP.adequate.mpr (run_output_call state originalCall owned expected found
    (code.lookup 0 rfl) (by cil_checked_step [formed]) (code.lookup 1 rfl) returnsNothing
    ⟨childFuel, result, invoked, rfl, valid.1.1, packed.trans correct,
      valid.1.writable (wordView output) (by simp), readable,
      fun id _ offset beyond => outside id offset beyond⟩)

end UInt256Proof.Multiply.BothTwo
namespace UInt256Proof.Multiply
@[simp] theorem lowProduct_zero_left (a : BitVec 64) : lowProduct (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by simp [lowProduct]
@[simp] theorem lowProduct_zero_right (a : BitVec 64) : lowProduct a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by simp [lowProduct]
@[simp] theorem highProduct_zero_left (a : BitVec 64) : highProduct (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by simp [highProduct]
@[simp] theorem highProduct_zero_right (a : BitVec 64) : highProduct a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by simp [highProduct]
@[simp] theorem sumHigh_zero_right (a : BitVec 64) : sumHigh a (BitVec.ofNat 64 0) = BitVec.ofNat 64 0 := by
  simp only [sumHigh, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
  rw [Nat.div_eq_of_lt a.isLt]
@[simp] theorem sumHigh_zero_left (a : BitVec 64) : sumHigh (BitVec.ofNat 64 0) a = BitVec.ofNat 64 0 := by
  simpa only [sumHigh, Nat.add_comm] using sumHigh_zero_right a
end UInt256Proof.Multiply
