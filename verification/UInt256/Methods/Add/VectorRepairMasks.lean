import UInt256.Methods.Add.VectorRepairSetup
import UInt256.Safety.NumericStore
import CIL.SIMD.Evaluation256Lemmas

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Convert a by-value vector argument to its sign mask and initialize the
    selected private word. Fetch premises bind this to the actual helper. -/
theorem repair_mask_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (pc argumentIndex localIndex : Nat) (spec : NumericLocalSpec)
    (specified : repairSpecs[localIndex]? = some spec) (kind : spec.kind = .word32)
    (vector : BitVec 256) (argument : args[argumentIndex]? = some (.scalar (.v256 vector)))
    (fetch0 : repairBody.code[pc]? = some (.arg argumentIndex))
    (fetch1 : repairBody.code[pc+1]? = some (.intrinsic (.vector (.reinterpret 256)) 1))
    (fetch2 : repairBody.code[pc+2]? = some (.intrinsic (.avx .moveMask64) 1))
    (fetch3 : repairBody.code[pc+3]? = some (.setLocal localIndex))
    (post : Memory → List Value → Prop)
    (continuation : ∀ home after,
      frame.locals[localIndex]? = some (.bytes .word32 home) →
      read after home 4 1 = .ok (numberBytes (CIL.Vector.moveMask64 vector).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current home (numberBytes (CIL.Vector.moveMask64 vector).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel repairIndex (pc+4) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel repairIndex pc args frame [] current = .ok (final, returned) ∧ post final returned := by
  have fits : localNumber spec.kind (.i32 (CIL.Vector.moveMask64 vector)) =
      .ok (CIL.Vector.moveMask64 vector).toNat := by rw [kind]; rfl
  obtain ⟨home, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store Extracted.program repairBody repairSpecs boundary entered current
      inputs outputs frame currentCall enteredWF homes authority localIndex spec specified
      (.i32 (CIL.Vector.moveMask64 vector)) (CIL.Vector.moveMask64 vector).toNat fits
  simp only [kind, localWidth] at slot loaded written
  have done := continuation home after slot loaded retained afterCall afterAuthority written
  have found : Extracted.program[repairIndex]? = some repairBody := by rfl
  have profile : repairBody.profile = Extracted.profile := by rfl
  apply run_next_exists post found fetch0
  · simp [step, argument, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found fetch1
  · simp [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
      CIL.Vector.intrinsic_reinterpret256, checkedValue, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found fetch2
  · simp [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
      CIL.Vector.intrinsic_movemask256, checkedValue, numericValue,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found fetch3
  · exact stored _ _ _
  simpa only [Nat.add_assoc] using done

/-- Check both extracted mask conversions, retaining the generated mask across
    the propagation-mask store. -/
theorem repair_masks_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary repairSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (generated propagation : BitVec 256)
    (generatedArgument : args[1]? = some (.scalar (.v256 generated)))
    (propagationArgument : args[2]? = some (.scalar (.v256 propagation)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ generatedHome propagationHome after,
      frame.locals[0]? = some (.bytes .word32 generatedHome) →
      frame.locals[1]? = some (.bytes .word32 propagationHome) →
      read after generatedHome 4 1 = .ok (numberBytes (CIL.Vector.moveMask64 generated).toNat 4) →
      read after propagationHome 4 1 = .ok (numberBytes (CIL.Vector.moveMask64 propagation).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel repairIndex 10 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel repairIndex 2 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply repair_mask_checked boundary entered current inputs outputs frame args currentCall enteredWF homes authority
    2 1 0 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl) rfl generated generatedArgument
    (by rfl) (by rfl) (by rfl) (by rfl) post
  intro generatedHome first generatedSlot generatedRead keep1 call1 auth1 write1
  apply repair_mask_checked boundary entered first inputs outputs frame args call1 enteredWF homes auth1
    6 2 1 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl) rfl propagation propagationArgument
    (by rfl) (by rfl) (by rfl) (by rfl) post
  intro propagationHome after propagationSlot propagationRead keep2 call2 auth2 write2
  have order := homes.ordered 0 1 .word32 .word32 generatedHome propagationHome
    (by decide) generatedSlot propagationSlot
  have retained := write_preserves_disjoint_read write2 generatedRead (Or.inl (Nat.ne_of_lt order))
  exact continuation generatedHome propagationHome after generatedSlot propagationSlot retained propagationRead
    (keep1.trans keep2) call2 auth2
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ write1).next
      (write_extends_allocations _ _ _ _ _ write2).next)

#print axioms repair_masks_checked
#print axioms repair_mask_checked
end UInt256Proof.Add.Safety
