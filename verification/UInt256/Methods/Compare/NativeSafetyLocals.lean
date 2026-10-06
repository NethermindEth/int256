import Extracted
import CIL.Safety.NumericHomes
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def nativeIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.avx512 _) _ => true | _ => false

def nativeBody : CIL.Method := Extracted.program[nativeIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def nativeUsesLess : Bool := nativeBody.code.any fun op =>
  match op with | .intrinsic (.avx512 .ltu64) _ => true | _ => false

def nativeInclusive : Bool := nativeBody.code.any fun op =>
  match op with | .const32 value => value == BitVec.ofNat 32 86 | _ => false

def nativeReturn : Nat := nativeBody.code.findIdx fun op =>
  match op with | .ret => true | _ => false

def nativeSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, by rfl⟩, ⟨.vector256, .v256 0, 0, by rfl⟩,
   ⟨.vector256, .v256 0, 0, by rfl⟩]

/-- Prepare the three extracted local homes with distinct identities, without
replacing caller inputs by disjoint synthetic values. -/
theorem native_setup (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ frame entered,
      enterFrame nativeBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity nativeSpecs frame.locals ∧
      CallingConditions Extracted.program entered [left, right] [] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity nativeSpecs call.1.1
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have kinds : nativeBody.localKinds = numericKinds nativeSpecs := by rfl
  have values : nativeBody.locals = numericInitializers nativeSpecs := by rfl
  have aggregates : nativeBody.aggregateArgs = [] := by rfl
  have setup : enterFrame nativeBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) := by
    simp [enterFrame, kinds, values, aggregates, made, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨frame, entered, setup, homes, call.after_frame_setup setup,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms native_setup
end UInt256Proof.Compare.Safety

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

/-- Three private writes retain caller bytes and the earlier local snapshots. -/
theorem native_local_writes (memory : Memory) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower nativeSpecs frame.locals)
    (vector : BitVec 256) (equal less : BitVec 256) :
    ∃ vectorRef equalRef lessRef first second final,
      frame.locals = [.bytes .vector256 vectorRef, .bytes .vector256 equalRef, .bytes .vector256 lessRef] ∧
      storeLocal memory (.bytes .vector256 vectorRef) (.scalar (.v256 vector)) =
        .ok (.bytes .vector256 vectorRef, first) ∧
      storeLocal first (.bytes .vector256 equalRef) (.scalar (.v256 equal)) =
        .ok (.bytes .vector256 equalRef, second) ∧
      storeLocal second (.bytes .vector256 lessRef) (.scalar (.v256 less)) =
        .ok (.bytes .vector256 lessRef, final) ∧
      loadLocal first (.bytes .vector256 vectorRef) = .ok (.scalar (.v256 vector)) ∧
      loadLocal second (.bytes .vector256 vectorRef) = .ok (.scalar (.v256 vector)) ∧
      loadLocal final (.bytes .vector256 equalRef) = .ok (.scalar (.v256 equal)) ∧
      loadLocal final (.bytes .vector256 lessRef) = .ok (.scalar (.v256 less)) ∧
      MemoryBelow lower memory first ∧ MemoryBelow lower memory second ∧
      MemoryBelow lower memory final := by
  rcases frame with ⟨activation, slots, owned, arguments⟩
  cases homes with
  | cons vectorRef vectorSpec vectorFresh vectorRead vectorAccess tail =>
    cases tail with
    | cons equalRef equalSpec equalFresh equalRead equalAccess tail =>
      cases tail with
      | cons lessRef lessSpec lessFresh lessRead lessAccess tail =>
        cases tail
        obtain ⟨first, w0, s0, r0⟩ := store_numeric_local .vector256 (.v256 vector) vector.toNat rfl vectorAccess
        obtain ⟨equalAllocation, equalReady⟩ := access_requirements equalAccess
        obtain ⟨lessAllocation, lessReady⟩ := access_requirements lessAccess
        obtain ⟨second, w1, s1, r1⟩ := store_numeric_local .vector256 (.v256 equal) equal.toNat rfl
          (equalReady.after_write w0).access
        obtain ⟨final, w2, s2, r2⟩ := store_numeric_local .vector256 (.v256 less) less.toNat rfl
          ((lessReady.after_write w0).after_write w1).access
        have ve : vectorRef.allocation < equalRef.allocation := equalFresh
        have el : equalRef.allocation < lessRef.allocation := lessFresh
        have r0after := write_preserves_disjoint_read w1 r0 (Or.inl (Nat.ne_of_lt ve))
        have r1after := write_preserves_disjoint_read w2 r1 (Or.inl (Nat.ne_of_lt el))
        have below0 := write_preserves_memory_below _ _ _ _ _ lower vectorFresh w0
        have below1 := write_preserves_memory_below _ _ _ _ _ lower
          (Nat.le_trans vectorFresh (Nat.le_of_lt ve)) w1
        have below2 := write_preserves_memory_below _ _ _ _ _ lower
          (Nat.le_trans vectorFresh (Nat.le_trans (Nat.le_of_lt ve) (Nat.le_of_lt el))) w2
        exact ⟨vectorRef, equalRef, lessRef, first, second, final, rfl, s0, s1, s2,
          load_numeric_local .vector256 (.v256 vector) vector.toNat rfl r0,
          load_numeric_local .vector256 (.v256 vector) vector.toNat rfl r0after,
          load_numeric_local .vector256 (.v256 equal) equal.toNat rfl r1after,
          load_numeric_local .vector256 (.v256 less) less.toNat rfl r2,
          below0, below0.trans below1, (below0.trans below1).trans below2⟩

#print axioms native_local_writes
end UInt256Proof.Compare.Safety
