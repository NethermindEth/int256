import UInt256.Methods.ConstructorSafety
import UInt256.Safety.ConstructorSetup
import UInt256.Safety.OutputReadability
import CIL.Safety.ConstructComposition
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Bitwise.ScalarSafety
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

def words (w0 w1 w2 w3 : BitVec 64) : List Value :=
  [.scalar (.i64 w0), .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)]

/-- Construct and store an initialized aggregate, then continue in the same frame. -/
theorem construct_prefix (program : CIL.Program) (index pc constructor : Nat)
    (body : CIL.Method) (profile : CIL.FeatureProfile)
    (found : program[index]? = some body)
    (constructorFound : program[constructor]? = some (UInt256Proof.ConstructorSafety.body profile))
    (fetched : body.code[pc]? = some (.newAggregate constructor 4 32))
    (storeFetched : body.code[pc + 1]? = some (.storeAggregate 32))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (args : List Value) (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ temporary : Reference, ∃ stored : Memory,
      temporary.allocation = memory.nextIdentity ∧
      CallingConditions program stored inputs [output] ∧
      read stored output 32 1 = .ok (numberBytes (packed w0 w1 w2 w3).toNat 32) ∧
      (∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        stored.cells id offset = memory.cells id offset) ∧
      ∀ final values,
        (∃ fuel, run program fuel index (pc + 2) args
          ⟨memory.nextIdentity, [], [temporary.allocation], []⟩ [] stored = .ok (final, values)) →
        ∃ fuel, run program fuel index pc args ⟨memory.nextIdentity, [], [], []⟩
          ((words w0 w1 w2 w3).reverse ++ [.reference (.address output)]) memory = .ok (final, values) := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have readonly : CallingConditions program memory inputs [] :=
    ⟨⟨call.1.1, call.1.2.1, by simp⟩, call.2⟩
  have checked : (words w0 w1 w2 w3).mapM (checkedValue memory) = .ok (words w0 w1 w2 w3) := by
    simp [words, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨temporary, updated, stepped, updatedCall, _, before, fresh⟩ :=
    readonly.new_aggregate256 (pc := pc) (callee := constructor)
      args (words w0 w1 w2 w3) [.reference (.address output)] frame memory found checked (by rfl)
  let nextFrame := { frame with owned := temporary.allocation :: frame.owned }
  have writable := call.1.2.2 (wordView output) (by simp)
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
  have old : output.allocation < memory.nextIdentity := (call.1.1.1 _ _ present).1
  have growth := step_extends_allocations _ _ _ _ _ _ _ _ stepped
  have updatedWritable := (before.access output old 32 1 true).trans writable
  obtain ⟨constructed, invoked, childCall, childOutside, authority, _, loaded⟩ :=
    constructor_contract profile program constructor constructorFound updated inputs temporary w0 w1 w2 w3 updatedCall
  have constructedWritable := authority.access updatedWritable (Nat.lt_of_lt_of_le old growth.next)
  have outputCall : CallingConditions program constructed inputs [output] :=
    ⟨⟨childCall.1.1, childCall.1.2.1, by simpa [wordView] using constructedWritable⟩, childCall.2⟩
  let bits := packed w0 w1 w2 w3
  have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨stored, written, storedCall, storedOutside, readback⟩ := outputCall.write_output_slice
    (by simp : output ∈ [output]) 0 (numberBytes bits.toNat 32)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  refine ⟨temporary, stored, fresh, storedCall, readback, ?_, ?_⟩
  · intro id bound offset outside
    have distinct : id ≠ temporary.allocation := by rw [fresh]; exact Nat.ne_of_lt bound
    exact (storedOutside id offset outside).trans
      ((childOutside id offset (Or.inl distinct)).trans (before.cells id bound offset))
  · intro final values continuation
    obtain ⟨fuel, continuation⟩ := continuation
    have tail : run program (fuel + 1) index (pc + 1) args nextFrame
        [.scalar (.aggregate (numberBytes bits.toNat 32)), .reference (.address output)] constructed =
        .ok (final, values) := by
      apply Eq.trans
      · apply run_next (target := pc + 2) (values := []) (nextFrame := nextFrame)
          (updated := stored) found storeFetched
        simp [step, cil_guard, observerCount, pureArity, instruction, referenceAt, length, written, checkedAt,
          Nat.add_assoc, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact continuation
    have child : invoke program 13 constructor
        (.reference (.address temporary) :: words w0 w1 w2 w3) updated = .ok (constructed, []) := invoked
    exact run_construct_exists found fetched stepped ⟨13, child⟩ loaded ⟨fuel + 1, tail⟩

#print axioms construct_prefix
theorem construct_result (program : CIL.Program) (scalarIndex constructPC constructorIndex : Nat)
    (scalarBody : CIL.Method) (profile : CIL.FeatureProfile)
    (found : program[scalarIndex]? = some scalarBody)
    (constructorFound : program[constructorIndex]? = some (body profile))
    (fetched : scalarBody.code[constructPC]? = some (.newAggregate constructorIndex 4 32))
    (storeFetched : scalarBody.code[constructPC + 1]? = some (.storeAggregate 32))
    (returnFetched : scalarBody.code[constructPC + 2]? = some .ret)
    (returns : scalarBody.returnsValue = false)
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (args : List Value) (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ fuel final,
      run program fuel scalarIndex constructPC args ⟨memory.nextIdentity, [], [], []⟩
        ((words w0 w1 w2 w3).reverse ++ [.reference (.address output)]) memory = .ok (final, []) ∧
      read final output 32 1 = .ok (numberBytes (packed w0 w1 w2 w3).toNat 32) ∧
      access final output 32 1 true = .ok () ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset := by
  obtain ⟨temporary, stored, fresh, storedCall, readback, outside, continuation⟩ :=
    construct_prefix program scalarIndex constructPC constructorIndex scalarBody profile found constructorFound
      fetched storeFetched memory inputs output args w0 w1 w2 w3 call
  let nextFrame : Frame := ⟨memory.nextIdentity, [], [temporary.allocation], []⟩
  have tail : run program 1 scalarIndex (constructPC + 2) args nextFrame [] stored =
      .ok (leaveFrame nextFrame stored, []) := by
    simp [run, found, returnFetched, returns, step, cil_guard, observerCount, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, finished⟩ := continuation _ [] ⟨1, tail⟩
  have after := leaveFrame_preserves_memory_below nextFrame stored memory.nextIdentity
    (by intro id member; simp only [nextFrame, List.mem_cons, List.not_mem_nil, or_false] at member
        rw [member, fresh]; exact Nat.le_refl _)
  have writable := call.1.2.2 (wordView output) (by simp)
  obtain ⟨allocation, present, _, _⟩ := access_within_allocation _ _ _ _ _ writable
  have old : output.allocation < memory.nextIdentity := (call.1.1.1 _ _ present).1
  refine ⟨fuel, _, finished, (after.read output old 32 1).trans readback,
    (after.access output old 32 1 true).trans (storedCall.1.2.2 (wordView output) (by simp)), ?_⟩
  intro id bound offset beyond
  exact (after.cells id bound offset).trans (outside id bound offset beyond)
#print axioms construct_result
end UInt256Proof.Bitwise.ScalarSafety
