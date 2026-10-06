import UInt256.Methods.Multiply.ScalarSafetyProducts
import UInt256.Methods.Multiply.StorageSafety
import UInt256.Methods.Multiply.ScalarValue
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

structure ScalarResult (original final : Memory) (input output : Reference)
    (word : BitVec 64) (returned : List Value) : Prop where
  returns : returned = []
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original input * BitVec.ofNat 256 word.toNat
  writable : access final output 32 1 true = .ok ()
  readable : ∃ bytes, read final output 32 1 = .ok bytes
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

theorem scalar_result_of_storage (original current result : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (valid : CallingConditions Extracted.program result [input] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (caller : ∀ id, id < original.nextIdentity → ∀ offset, current.cells id offset = original.cells id offset)
    (value : inputValue result output = inputValue original input * BitVec.ofNat 256 word.toNat)
    (readable : ∃ bytes, read result output 32 1 = .ok bytes)
    (outside : ∀ id offset, OutsideOutput output id offset → result.cells id offset = current.cells id offset) :
    ScalarResult original (leaveFrame frame result) input output word [] := by
  have retained := leaveFrame_preserves_memory_below frame result original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _
    (originalCall.output_formed (by simp : output ∈ [output]))
  have old := (originalCall.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame result).cells output.allocation offset).bits) =
      (fun offset => (result.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation old offset]
  refine ⟨rfl, leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_,
    (retained.access output old 32 1 true).trans (valid.1.2.2 (wordView output) (by simp)), ?_, ?_⟩
  · simpa only [inputValue, bytes] using value
  · obtain ⟨snapshot, loaded⟩ := readable
    exact ⟨snapshot, (retained.read output old 32 1).trans loaded⟩
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (caller id old offset))

theorem scalar_output (original entered current : Memory) (input output : Reference)
    (word : BitVec 64) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity scalarBody.localKinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : PrivateWords Extracted.program original entered current [input] [output] frame
      (scalarProducts original input word)) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 66 (scalarArgs input word output) frame
        [.scalar (.i64 (inputLimb original input 3))] current = .ok (final, returned) ∧
      ScalarResult original final input output word returned := by
  let words := scalarLimbs (inputLimb original input) word
  let carry := scalarCarry word (inputLimb original input 2)
    (scalarCarry word (inputLimb original input 1) (highProduct word (inputLimb original input 0)))
  let post := fun final returned => ScalarResult original final input output word returned
  have loadCarry := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := scalarBody) (args := scalarArgs input word output) (pc := pc) (stack := stack)
    (index := 3) carry (by simp [scalarProducts, ladderWords, rememberWord, carry, scalarCarry])
  obtain ⟨prepared, storedLast, preparedState⟩ := state.store enteredWF homes 8 (by rfl) (words 3)
    70 (scalarArgs input word output) [] (body := scalarBody)
  have lastValue : words 3 = inputLimb original input 3 * word + carry := by
    simp [words, scalarLimbs, CIL.fin_val_three, lowProduct, carry, BitVec.mul_comm]
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  change ∃ fuel final returned, _ ∧ post final returned
  iterate 4
    apply run_next_exists post found (by rfl)
    first
    | exact loadCarry _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, scalarArgs, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl)
  · simpa only [lastValue] using storedLast
  have formed := preparedState.call.output_formed (by simp : output ∈ [output])
  have load (index : Fin 4) (pc : Nat) (stack : List Value) :
      step scalarBody (.local (if index = 0 then 4 else 5 + index.val)) pc
        (scalarArgs input word output) frame stack prepared =
        .ok (.next (pc + 1) (.scalar (.i64 (words index)) :: stack) frame prepared) := by
    apply preparedState.snapshots.load
    obtain ⟨i, bound⟩ := index
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [words, scalarLimbs, scalarProducts, ladderWords, scalarFirstProduct,
        scalarInputs, rememberWord, scalarCarry]
  iterate 5
    apply run_next_exists post found (by rfl)
    first
    | exact load 0 _ _
    | exact load 1 _ _
    | exact load 2 _ _
    | exact load 3 _ _
    | simp [step, scalarArgs, checkedValue, numericValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
    store_product_contract prepared [input] output (words 0) (words 1) (words 2) (words 3) preparedState.call
  have stepped : step scalarBody (.call productStoreIndex 5) 76 (scalarArgs input word output) frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)), .scalar (.i64 (words 0)),
        .reference (.address output)] prepared =
      .ok (.call productStoreIndex
        [.reference (.address output), .scalar (.i64 (words 0)), .scalar (.i64 (words 1)), .scalar (.i64 (words 2)),
          .scalar (.i64 (words 3))] [] prepared) := by
    simp [step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have finished : run Extracted.program 1 scalarIndex 77 (scalarArgs input word output) frame [] result =
      .ok (leaveFrame frame result, []) := by
    have fetched : scalarBody.code[77]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  obtain ⟨fuel, ran⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, finished⟩
  have mathematical := scalar_limbs_correct (inputLimb original input) word
  rw [input_limbs_value] at mathematical
  have packed : inputValue result output = UInt256Model.value words := value
  exact ⟨fuel, leaveFrame frame result, [], ran, scalar_result_of_storage original prepared result input output word frame
    originalCall valid owned preparedState.caller (packed.trans mathematical) readable outside⟩

#print axioms scalar_output
end UInt256Proof.Multiply.Safety
