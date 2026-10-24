import CIL.Safety.NumericHomes
import UInt256.Safety.ReadOnlyExecution
namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety
def portableBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [.v256 0, .i32 0, .i32 0], localKinds := [.vector256, .word32, .word32], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .arg 1,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .setLocal 0,
  .dup,
  .local 0,
  .intrinsic (.vector (.eq64 256)) 2,
  .intrinsic (.vector (.extractMSB64 256)) 1,
  .setLocal 1,
  .local 0,
  .intrinsic (.vector (.ltu64 256)) 2,
  .intrinsic (.vector (.extractMSB64 256)) 1,
  .setLocal 2,
  .local 1,
  .local 2,
  .call callee 2,
  .ret (some .unsigned8)] }
def portableSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, by rfl⟩, ⟨.word32, .i32 0, 0, by rfl⟩,
   ⟨.word32, .i32 0, 0, by rfl⟩]

/-- Prepare the three extracted local homes with distinct identities, without
replacing caller inputs by disjoint synthetic values. -/
theorem portable_setup (profile : CIL.FeatureProfile) (callee : Nat) (program : CIL.Program) (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ frame entered,
      enterFrame (portableBody profile callee) (readOnlyArguments [left, right]) memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity portableSpecs frame.locals ∧
      CallingConditions program entered [left, right] [] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity portableSpecs call.1.1
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have kinds : (portableBody profile callee).localKinds = numericKinds portableSpecs := by rfl
  have values : (portableBody profile callee).locals = numericInitializers portableSpecs := by rfl
  have aggregates : (portableBody profile callee).vectorArgs = [] := by rfl
  have parameters : (portableBody profile callee).parameterHomes = [] := rfl
  have opaqueLocals : (portableBody profile callee).opaqueVectorLocals = [] := rfl
  have setup : enterFrame (portableBody profile callee) (readOnlyArguments [left, right]) memory = .ok (frame, entered) := by
    simp [enterFrame, opaqueLocals, makeSelectedLocals, kinds, values, aggregates, made, makeArgumentHomes, parameters, makeParameterHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨frame, entered, setup, homes, call.after_frame_setup setup,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms portable_setup
end UInt256Proof.Compare.Safety

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

/-- Three private writes retain caller bytes and the earlier local snapshots. -/
theorem portable_local_writes (memory : Memory) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower portableSpecs frame.locals)
    (vector : BitVec 256) (equal less : BitVec 32) :
    ∃ vectorRef equalRef lessRef first second final,
      frame.locals = [.bytes .vector256 vectorRef, .bytes .word32 equalRef, .bytes .word32 lessRef] ∧
      storeLocal memory (.bytes .vector256 vectorRef) (.scalar (.v256 vector)) =
        .ok (.bytes .vector256 vectorRef, first) ∧
      storeLocal first (.bytes .word32 equalRef) (.scalar (.i32 equal)) =
        .ok (.bytes .word32 equalRef, second) ∧
      storeLocal second (.bytes .word32 lessRef) (.scalar (.i32 less)) =
        .ok (.bytes .word32 lessRef, final) ∧
      loadLocal first (.bytes .vector256 vectorRef) = .ok (.scalar (.v256 vector)) ∧
      loadLocal second (.bytes .vector256 vectorRef) = .ok (.scalar (.v256 vector)) ∧
      loadLocal final (.bytes .word32 equalRef) = .ok (.scalar (.i32 equal)) ∧
      loadLocal final (.bytes .word32 lessRef) = .ok (.scalar (.i32 less)) ∧
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
        obtain ⟨second, w1, s1, r1⟩ := store_numeric_local .word32 (.i32 equal) equal.toNat rfl
          (equalReady.after_write w0).access
        obtain ⟨final, w2, s2, r2⟩ := store_numeric_local .word32 (.i32 less) less.toNat rfl
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
          load_numeric_local .word32 (.i32 equal) equal.toNat rfl r1after,
          load_numeric_local .word32 (.i32 less) less.toNat rfl r2,
          below0, below0.trans below1, (below0.trans below1).trans below2⟩

#print axioms portable_local_writes
end UInt256Proof.Compare.Safety
