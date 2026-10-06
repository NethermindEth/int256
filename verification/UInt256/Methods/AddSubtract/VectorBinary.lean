import UInt256.Methods.AddSubtract.VectorOperands

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- A fetched binary vector operation followed by a private store preserves
    both operand homes and all caller memory. -/
theorem vector_binary_checked (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftHome rightHome : Reference) (a b : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (pc destination : Nat) (later : 1 < destination)
    (operation : CIL.Intrinsic) (value : BitVec 256)
    (specified : vectorSpecs[destination]? = some vectorZeroSpec)
    (available : operation.available vectorBody.profile = true)
    (evaluated : CIL.evalIntrinsic operation [.v256 a, .v256 b] = some (.v256 value))
    (fetchLeft : vectorBody.code[pc]? = some (.local 0))
    (fetchRight : vectorBody.code[pc + 1]? = some (.local 1))
    (fetchOperation : vectorBody.code[pc + 2]? = some (.intrinsic operation 2))
    (fetchStore : vectorBody.code[pc + 3]? = some (.setLocal destination))
    (post : Memory → List Value → Prop)
    (continuation : ∀ resultHome after,
      frame.locals[destination]? = some (.bytes .vector256 resultHome) →
      read after resultHome 32 1 = .ok (numberBytes value.toNat 32) →
      read after leftHome 32 1 = .ok (numberBytes a.toNat 32) →
      read after rightHome 32 1 = .ok (numberBytes b.toNat 32) →
      MemoryBelow original.nextIdentity current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      MemoryBelow resultHome.allocation current after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (pc + 4) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex pc args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨resultHome, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector_local_store original.nextIdentity entered current inputs outputs frame currentCall enteredWF
      homes authority destination vectorZeroSpec specified (.v256 value)
      value.toNat rfl
  have leftOrder := homes.ordered 0 destination .vector256 .vector256 leftHome resultHome (by omega) leftSlot slot
  have rightOrder := homes.ordered 1 destination .vector256 .vector256 rightHome resultHome later rightSlot slot
  have retainedLeft := write_preserves_disjoint_read written leftRead (Or.inl (Nat.ne_of_lt leftOrder))
  have retainedRight := write_preserves_disjoint_read written rightRead (Or.inl (Nat.ne_of_lt rightOrder))
  have earlier := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_refl resultHome.allocation) written
  have done := continuation resultHome after slot loaded retainedLeft retainedRight retained afterCall afterAuthority earlier
    (write_extends_allocations _ _ _ _ _ written).next
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 a) a.toNat rfl leftSlot leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 b) b.toNat rfl rightSlot rightRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  apply run_next_exists post found fetchLeft (loadLeft _ _)
  apply run_next_exists post found fetchRight (loadRight _ _)
  apply run_next_exists (target := pc + 3) (values := [.scalar (.v256 value)]) (nextFrame := frame) (updated := current) post found fetchOperation
  · simp (config := { implicitDefEqProofs := false })
      [step, pureArity, scalars, CIL.step, available, evaluated, checkedValue,
        numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · apply run_next_exists post found fetchStore (stored _ _ _)
    exact done

#print axioms vector_binary_checked
end UInt256Proof.AddSubtract.Safety
