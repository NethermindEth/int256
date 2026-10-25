import UInt256.Methods.Compare.NativeLocals
import UInt256.Methods.Compare.VectorMasks
import UInt256.Methods.Equality.VectorPrimitive
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety
def nativeEqual (left right : BitVec 256) : BitVec 256 :=
  (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) left right)
def nativeComparison (usesLess : Bool) (left right : BitVec 256) : BitVec 256 :=
  (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (if usesLess then x.ult y else y.ult x)) left right)

def nativeResult (usesLess inclusive : Bool) (left right : BitVec 256) : BitVec 32 :=
  if ((CIL.Vector.moveMask32 (CIL.Vector.blend32 (nativeEqual left right)
      (nativeComparison usesLess left right) 170)) - (if inclusive then 86 else 85)).toInt < 0 then 1 else 0

private theorem native_arg_first {body : CIL.Method} {pc : Nat} {rest stack : List Value} {frame : Frame}
    {memory : Memory} {input : Reference} (formed : form memory input = .ok input) :
    step body (.arg 0) pc (.reference (.address input) :: rest) frame stack memory =
      .ok (.next (pc + 1) (.reference (.address input) :: stack) frame memory) := by
  have checked : checkedValue memory (.reference (.address input)) = .ok (.reference (.address input)) := by
    simp only [checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  show (checkedValue memory (.reference (.address input))).bind _ = _
  rw [checked]; rfl

private theorem native_arg_second {body : CIL.Method} {pc : Nat} {first : Value} {rest stack : List Value}
    {frame : Frame} {memory : Memory} {input : Reference} (formed : form memory input = .ok input) :
    step body (.arg 1) pc (first :: .reference (.address input) :: rest) frame stack memory =
      .ok (.next (pc + 1) (.reference (.address input) :: stack) frame memory) := by
  have checked : checkedValue memory (.reference (.address input)) = .ok (.reference (.address input)) := by
    simp only [checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  show (checkedValue memory (.reference (.address input))).bind _ = _
  rw [checked]; rfl

private theorem native_load {body : CIL.Method} {pc : Nat} {args rest values : List Value} {frame : Frame}
    {memory updated : Memory} {reference : ManagedReference}
    (loaded : instruction (.loadAggregate 32) (.reference reference :: rest) memory = .ok (updated, values)) :
    step body (.loadAggregate 32) pc args frame (.reference reference :: rest) memory =
      .ok (.next (pc + 1) values frame updated) := by
  simp only [cil_step, instructionStep, loaded, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem native_bitcast {body : CIL.Method} {pc : Nat} {args rest values : List Value} {frame : Frame}
    {memory updated : Memory} {value : CIL.Value} {source target : CIL.SnapshotShape}
    (cast : memoryInstruction (.bitcastValue source target) (.scalar value :: rest) memory = .ok (updated, values)) :
    step body (.memory (.bitcastValue source target)) pc args frame (.scalar value :: rest) memory =
      .ok (.next (pc + 1) values frame updated) := by
  have known : unspecifiedOperands (CIL.MemoryOp.bitcastValue source target).argumentCount (.scalar value :: rest) = false := by
    cases observed : unspecifiedOperands (CIL.MemoryOp.bitcastValue source target).argumentCount (.scalar value :: rest)
    · rfl
    · unfold memoryInstruction at cast
      simp only [observed, ite_true] at cast
      cases cast
  rw [step_memory_eq]
  simp only [known, staticInstruction, cast, Bool.false_eq_true, ite_false, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

private theorem native_store0 {body : CIL.Method} {pc activation stackBytes : Nat} {owned : List AllocationId}
    {arguments : List (Nat × LocalSlot)} {args rest : List Value} {value : Value} {memory updated : Memory}
    {slot0 slot1 slot2 : LocalSlot} (stored : storeLocal memory slot0 value = .ok (slot0, updated)) :
    step body (.setLocal 0) pc args {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } (value :: rest) memory =
      .ok (.next (pc + 1) rest {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } updated) := by
  show (storeLocal memory slot0 value).bind _ = _
  rw [stored]; rfl

private theorem native_store1 {body : CIL.Method} {pc activation stackBytes : Nat} {owned : List AllocationId}
    {arguments : List (Nat × LocalSlot)} {args rest : List Value} {value : Value} {memory updated : Memory}
    {slot0 slot1 slot2 : LocalSlot} (stored : storeLocal memory slot1 value = .ok (slot1, updated)) :
    step body (.setLocal 1) pc args {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } (value :: rest) memory =
      .ok (.next (pc + 1) rest {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } updated) := by
  show (storeLocal memory slot1 value).bind _ = _
  rw [stored]; rfl

private theorem native_store2 {body : CIL.Method} {pc activation stackBytes : Nat} {owned : List AllocationId}
    {arguments : List (Nat × LocalSlot)} {args rest : List Value} {value : Value} {memory updated : Memory}
    {slot0 slot1 slot2 : LocalSlot} (stored : storeLocal memory slot2 value = .ok (slot2, updated)) :
    step body (.setLocal 2) pc args {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } (value :: rest) memory =
      .ok (.next (pc + 1) rest {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } updated) := by
  show (storeLocal memory slot2 value).bind _ = _
  rw [stored]; rfl

private theorem native_read0 {body : CIL.Method} {pc activation stackBytes : Nat} {owned : List AllocationId}
    {arguments : List (Nat × LocalSlot)} {args stack : List Value} {value : Value} {memory : Memory}
    {slot0 slot1 slot2 : LocalSlot} (loaded : loadLocal memory slot0 = .ok value) :
    step body (.local 0) pc args {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } stack memory =
      .ok (.next (pc + 1) (value :: stack) {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } memory) := by
  show (loadLocal memory slot0).bind _ = _
  rw [loaded]; rfl

private theorem native_read1 {body : CIL.Method} {pc activation stackBytes : Nat} {owned : List AllocationId}
    {arguments : List (Nat × LocalSlot)} {args stack : List Value} {value : Value} {memory : Memory}
    {slot0 slot1 slot2 : LocalSlot} (loaded : loadLocal memory slot1 = .ok value) :
    step body (.local 1) pc args {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } stack memory =
      .ok (.next (pc + 1) (value :: stack) {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } memory) := by
  show (loadLocal memory slot1).bind _ = _
  rw [loaded]; rfl

private theorem native_read2 {body : CIL.Method} {pc activation stackBytes : Nat} {owned : List AllocationId}
    {arguments : List (Nat × LocalSlot)} {args stack : List Value} {value : Value} {memory : Memory}
    {slot0 slot1 slot2 : LocalSlot} (loaded : loadLocal memory slot2 = .ok value) :
    step body (.local 2) pc args {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } stack memory =
      .ok (.next (pc + 1) (value :: stack) {
        activation := activation
        locals := [slot0, slot1, slot2]
        owned := owned
        arguments := arguments
        stackBytes := stackBytes } memory) := by
  show (loadLocal memory slot2).bind _ = _
  rw [loaded]; rfl

set_option hygiene false in
/-- One instruction step; failed alternatives stay reducible so they never unfold memory. -/
macro "native_step" : tactic =>
  `(tactic| refine (run_next found rfl (by
      first
        | (with_reducible exact native_arg_first fl)
        | (with_reducible exact native_arg_second fr)
        | ((with_reducible apply native_load); first | with_reducible exact hl _ | with_reducible exact hr _)
        | ((with_reducible apply native_bitcast); first | with_reducible exact cl _ | with_reducible exact cr _)
        | ((with_reducible apply native_store0); exact s0)
        | ((with_reducible apply native_store1); exact s1)
        | ((with_reducible apply native_store2); exact s2)
        | ((with_reducible apply native_read0); first | with_reducible exact r0 | with_reducible exact r0after)
        | ((with_reducible apply native_read1); exact r1)
        | ((with_reducible apply native_read2); exact r2)
        | rfl)).trans ?_)

theorem native_run (profile : CIL.FeatureProfile) (usesLess inclusive : Bool) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (nativeBody profile usesLess inclusive))
    (native : profile.avx512FVL = true) (nativeF : profile.avx512F = true) (avx2 : profile.avx2 = true) (avx : profile.avx = true)
    (memory : Memory) (left right : Reference) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower nativeSpecs frame.locals)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
        .ok (leaveFrame frame final, [.scalar (.i32 (nativeResult usesLess inclusive (inputValue memory left) (inputValue memory right)))]) ∧
      MemoryBelow lower memory final := by
  let x := inputValue memory left
  let y := inputValue memory right
  let eqWord := nativeEqual x y
  let ltWord := nativeComparison usesLess x y
  obtain ⟨vr, er, lr, m0, m1, m2, slots, s0, s1, s2, r0, r0after, r1, r2, _, _, preserved⟩ :=
    native_local_writes memory frame lower homes y eqWord ltWord
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := UInt256Proof.Equality.VectorPrimitive.load_input call (by simp : left ∈ [left, right])
  have cl := UInt256Proof.Equality.VectorPrimitive.cast_input memory left
  have hr := UInt256Proof.Equality.VectorPrimitive.load_input call (by simp : right ∈ [left, right])
  have cr := UInt256Proof.Equality.VectorPrimitive.cast_input memory right
  simp only [eqWord, ltWord, nativeEqual, nativeComparison, x, y] at *
  clear eqWord ltWord x y
  generalize leftValue : inputValue memory left = leftBits at *
  generalize rightValue : inputValue memory right = rightBits at *
  refine ⟨(if inclusive then 28 else 27) + 1, m2, ?_, preserved⟩
  rcases frame with ⟨activation, locals, owned, arguments, stackBytes⟩
  dsimp only at slots
  subst slots
  cases profile
  dsimp only at native nativeF avx2 avx
  subst native nativeF avx2 avx
  simp only [readOnlyArguments, List.map]
  cases usesLess <;> cases inclusive <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  all_goals
    repeat native_step
    refine (run_return found rfl rfl rfl).trans ?_
    simp only [nativeResult, nativeEqual, nativeComparison, Bool.false_eq_true, ite_true, ite_false]
    split <;> split <;> first | rfl | (rename_i a b; exact absurd a b) | (rename_i a b; exact absurd b a)
#print axioms native_run
end UInt256Proof.Compare.Safety
