import Extracted
import CIL.Safety.StepComposition
import UInt256.Safety.NumericStore
import UInt256.Arithmetic.CascadeVectors

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- The extracted method containing the bounded correction-table access. -/
def cascadeMethodIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .memory .spanReference => true | _ => false

def cascadeBody : CIL.Method := Extracted.program[cascadeMethodIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def cascadeSpecs : List NumericLocalSpec := numericSpecs cascadeBody

def cascadeStart : Nat := (cascadeBody.code.findIdx fun op => match op with
  | .mul => true | _ => false) - 3

def cascadeSumSlot : Nat := match cascadeBody.code[cascadeStart+2]? with
  | some (.local index) => index | _ => 0

def cascadeIndexSlot : Nat := match cascadeBody.code[cascadeStart]? with
  | some (.local index) => index | _ => 0

def cascadeWordZero : NumericLocalSpec := ⟨.word32, .i32 0, 0, rfl⟩

/-- Checked scalar index arithmetic, including both overwrites of slot seven.
    Its final mask proves the lookup index is below sixteen. -/
theorem cascade_index_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary cascadeSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (generatedHome equalHome : Reference) (generated equal : BitVec 32)
    (generatedSlot : frame.locals[cascadeSumSlot]? = some (.bytes .word32 generatedHome))
    (equalSlot : frame.locals[cascadeIndexSlot]? = some (.bytes .word32 equalHome))
    (generatedRead : read current generatedHome 4 1 = .ok (numberBytes generated.toNat 4))
    (equalRead : read current equalHome 4 1 = .ok (numberBytes equal.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∀ sumHome indexHome after,
      frame.locals[cascadeSumSlot]? = some (.bytes .word32 sumHome) →
      frame.locals[cascadeIndexSlot]? = some (.bytes .word32 indexHome) →
      read after sumHome 4 1 = .ok (numberBytes (equal + 2 * generated).toNat 4) →
      read after indexHome 4 1 = .ok (numberBytes (UInt256Proof.SIMD.cascadeIndex generated equal).toNat 4) →
      (UInt256Proof.SIMD.cascadeIndex generated equal).toNat < 16 →
      MemoryBelow sumHome.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel cascadeMethodIndex (cascadeStart + 14) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel cascadeMethodIndex cascadeStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨sumHome, m1, sumSlot, sumRead, keep1, call1, auth1, write1, store1⟩ :=
    checked_numeric_store Extracted.program cascadeBody cascadeSpecs boundary entered current inputs outputs frame currentCall enteredWF homes authority
      cascadeSumSlot cascadeWordZero (by rfl) (.i32 (equal + 2 * generated)) (equal + 2 * generated).toNat rfl
  have equalOrder := homes.ordered cascadeSumSlot cascadeIndexSlot .word32 .word32 sumHome equalHome (by decide) sumSlot equalSlot
  have equalRead1 := write_preserves_disjoint_read write1 equalRead (Or.inl (Ne.symm (Nat.ne_of_lt equalOrder)))
  obtain ⟨xorHome, m2, xorSlot, xorRead, keep2, call2, auth2, write2, store2⟩ :=
    checked_numeric_store Extracted.program cascadeBody cascadeSpecs boundary entered m1 inputs outputs frame call1 enteredWF homes auth1
      cascadeIndexSlot cascadeWordZero (by rfl) (.i32 (equal ^^^ (equal + 2 * generated)))
      (equal ^^^ (equal + 2 * generated)).toNat rfl
  have xorOrder := homes.ordered cascadeSumSlot cascadeIndexSlot .word32 .word32 sumHome xorHome (by decide) sumSlot xorSlot
  have sumRead2 := write_preserves_disjoint_read write2 sumRead (Or.inl (Nat.ne_of_lt xorOrder))
  obtain ⟨indexHome, m3, indexSlot, indexRead, keep3, call3, auth3, write3, store3⟩ :=
    checked_numeric_store Extracted.program cascadeBody cascadeSpecs boundary entered m2 inputs outputs frame call2 enteredWF homes auth2
      cascadeIndexSlot cascadeWordZero (by rfl) (.i32 (UInt256Proof.SIMD.cascadeIndex generated equal))
      (UInt256Proof.SIMD.cascadeIndex generated equal).toNat rfl
  have indexOrder := homes.ordered cascadeSumSlot cascadeIndexSlot .word32 .word32 sumHome indexHome (by decide) sumSlot indexSlot
  have sumRead3 := write_preserves_disjoint_read write3 sumRead2 (Or.inl (Nat.ne_of_lt indexOrder))
  have earlier1 := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_refl sumHome.allocation) write1
  have earlier2 := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_of_lt xorOrder) write2
  have earlier3 := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_of_lt indexOrder) write3
  have done := continuation sumHome indexHome m3 sumSlot indexSlot sumRead3 indexRead
    (UInt256Proof.SIMD.cascade_index_bound generated equal) (earlier1.trans (earlier2.trans earlier3))
    (keep1.trans (keep2.trans keep3)) call3 auth3
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ write1).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ write2).next
        (write_extends_allocations _ _ _ _ _ write3).next))
  have loadGenerated := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := cascadeBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 generated) generated.toNat rfl generatedSlot generatedRead
  have loadEqual := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := cascadeBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 equal) equal.toNat rfl equalSlot equalRead
  have loadEqual1 := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := cascadeBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 equal) equal.toNat rfl equalSlot equalRead1
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := cascadeBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 (equal + 2 * generated)) (equal + 2 * generated).toNat rfl sumSlot sumRead
  have loadXor := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := cascadeBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 (equal ^^^ (equal + 2 * generated))) (equal ^^^ (equal + 2 * generated)).toNat rfl xorSlot xorRead
  have found : Extracted.program[cascadeMethodIndex]? = some cascadeBody := by rfl
  conv at done in cascadeStart => cbv
  conv in cascadeStart => cbv
  have sumIndex : cascadeSumSlot = cascadeSumSlot := rfl
  conv at sumIndex => rhs; cbv
  have indexIndex : cascadeIndexSlot = cascadeIndexSlot := rfl
  conv at indexIndex => rhs; cbv
  simp only [sumIndex, indexIndex] at *
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact store1 _ _ _
       | exact store2 _ _ _
       | exact store3 _ _ _
       | exact loadGenerated _ _
       | exact loadEqual _ _
       | exact loadEqual1 _ _
       | exact loadSum _ _
       | exact loadXor _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms cascade_index_checked
end UInt256Proof.AddSubtract.Safety
