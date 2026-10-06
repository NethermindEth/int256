import UInt256.Methods.Subtract.VectorSafetyOutput

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vectorTestStart : Nat := (vectorBody.code.findIdx fun op =>
  match op with | .intrinsic (.avx .testZ64) 2 => true | _ => false) - 2

def vectorFastReturn : Nat := match vectorBody.code[vectorTestStart + 3]? with
  | some (.brnonzero target) => target
  | _ => 0

/-- Branch on the actual saved propagation mask without reading caller inputs. -/
theorem vector_propagation_test (memory : Memory) (frame : Frame) (args : List Value)
    (equalHome incomingHome : Reference) (equal incoming : BitVec 256)
    (equalSlot : frame.locals[5]? = some (.bytes .vector256 equalHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (equalRead : read memory equalHome 32 1 = .ok (numberBytes equal.toNat 32))
    (incomingRead : read memory incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vectorIndex
        (if equal &&& incoming = 0 then vectorFastReturn else vectorTestStart + 4)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorTestStart args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have loadEqual := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 equal) equal.toNat rfl equalSlot equalRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 incoming) incoming.toNat rfl incomingSlot incomingRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  have testPC : vectorTestStart = vectorTestStart := rfl
  conv at testPC => rhs; cbv
  have returnPC : vectorFastReturn = vectorFastReturn := rfl
  conv at returnPC => rhs; cbv
  simp only [testPC, returnPC] at continuation
  rw [testPC]
  by_cases zero : equal &&& incoming = BitVec.ofNat 256 0
  all_goals
    simp only [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, zero, ite_true, ite_false] at continuation
    repeat' first
      | (simpa [zero] using continuation)
      | (simp (config := { failIfUnchanged := false }) [zero]
         apply run_next_exists post found (by rfl)
         first
         | exact loadEqual _ _
         | exact loadIncoming _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_testz256, zero, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_propagation_test

def equalLanes (a b : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) a b

/-- Generate the equality mask from saved operands, then take the checked
    propagation branch. No caller input load occurs after the output write. -/
theorem vector_propagation_checked (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (leftHome rightHome incomingHome : Reference) (a b incoming : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ equalHome after,
      frame.locals[5]? = some (.bytes .vector256 equalHome) →
      read after equalHome 32 1 = .ok (numberBytes (equalLanes a b).toNat 32) →
      MemoryBelow original.nextIdentity current after →
      MemoryBelow equalHome.allocation current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex
          (if equalLanes a b &&& incoming = 0 then vectorFastReturn else vectorTestStart + 4)
          args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  apply vector_binary_checked original entered current inputs outputs frame args currentCall
    enteredWF homes authority leftHome rightHome a b leftSlot rightSlot leftRead rightRead
    (vectorOutputStart + 8) 5 (by decide) (.vector (.eq64 256)) (equalLanes a b)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) post
  intro equalHome after equalSlot equalRead _ _ preserved afterCall afterAuthority earlier advanced
  have order := homes.ordered 4 5 .vector256 .vector256 incomingHome equalHome
    (by decide) incomingSlot equalSlot
  have retainedIncoming := (earlier.read incomingHome order 32 1).trans incomingRead
  exact vector_propagation_test after frame args equalHome incomingHome (equalLanes a b) incoming
    equalSlot incomingSlot equalRead retainedIncoming post
    (continuation equalHome after equalSlot equalRead preserved earlier afterCall afterAuthority advanced)

#print axioms vector_propagation_checked
end UInt256Proof.Subtract.Safety
