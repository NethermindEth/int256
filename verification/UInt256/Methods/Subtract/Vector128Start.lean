import CIL.Safety.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.AddSubtract.Vector128Incoming

/-!
Vector128 subtraction between its saved operand halves and the fast/repair branch: the lane
differences and borrow masks, and the coalesced propagation test.
-/

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def subtractStartCode : List CIL.Op := [
  .local 1, .local 3, .intrinsic (.vector (.sub64 128)) 2, .setLocal 5,
  .local 2, .local 4, .intrinsic (.vector (.sub64 128)) 2, .setLocal 6,
  .local 1, .local 3, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 7,
  .local 2, .local 4, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 8]

def subtractDecisionCode : List CIL.Op := [
  .local 5, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 9, .intrinsic (.vector (.band 128)) 2,
  .local 6, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 10, .intrinsic (.vector (.band 128)) 2,
  .intrinsic (.vector (.bor 128)) 2,
  .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero 119]

def subtractMask (a b : BitVec 128) : BitVec 128 := zip128 (fun x y => mask64 (x.ult y)) a b

/-- Initial halves, lane differences, borrow masks and the two incoming-borrow vectors. -/
def subtractSnapshot (values : Fin 4 → BitVec 128) (i : Nat) : BitVec 128 :=
  if h : i < 4 then values ⟨i, h⟩
  else if i = 4 then zip128 (· - ·) (values 0) (values 2)
  else if i = 5 then zip128 (· - ·) (values 1) (values 3)
  else if i = 6 then subtractMask (values 0) (values 2)
  else if i = 7 then subtractMask (values 1) (values 3)
  else if i = 8 then incoming128Low (subtractMask (values 0) (values 2))
  else incoming128High (subtractMask (values 0) (values 2)) (subtractMask (values 1) (values 3))

def subtractPropagation (values : Fin 4 → BitVec 128) : BitVec 128 :=
  (zip128 (fun x y => mask64 (x == y)) (subtractSnapshot values 4) 0 &&&
      subtractSnapshot values 8) |||
    (zip128 (fun x y => mask64 (x == y)) (subtractSnapshot values 5) 0 &&&
      subtractSnapshot values 9)

/-- Lane differences and borrow masks from the four saved halves. -/
theorem subtract_start_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body)
    (code : CodeAt body 22 subtractStartCode)
    (vectorSpecs : ∀ i : Fin 10, specs[i.val]? = some vector128ZeroSpec)
    (original entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (values : Fin 4 → BitVec 128)
    (state : VectorState program original.nextIdentity original entered current inputs outputs
      slots (subtractSnapshot values) 4)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program original.nextIdentity original entered after inputs outputs slots
        (subtractSnapshot values) 8 →
      ∃ fuel result returned,
        run program fuel method 38 args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current = .ok (result, returned) ∧
        post result returned := by
  have store := fun current done (state : VectorState program original.nextIdentity original
      entered current inputs outputs slots (subtractSnapshot values) done) (declared : done < 10)
      stored same =>
    state.store body specs frame root layout enteredWF homes (vectorSpecs ⟨done, declared⟩)
      stored same
  obtain ⟨m4, s5, st4⟩ := store _ 4 state (by decide)
    (zip128 (· - ·) (subtractSnapshot values 0) (subtractSnapshot values 2)) rfl
  obtain ⟨m5, s6, st5⟩ := store _ 5 s5 (by decide)
    (zip128 (· - ·) (subtractSnapshot values 1) (subtractSnapshot values 3)) rfl
  obtain ⟨m6, s7, st6⟩ := store _ 6 s6 (by decide)
    (subtractMask (subtractSnapshot values 0) (subtractSnapshot values 2)) rfl
  obtain ⟨m7, s8, st7⟩ := store _ 7 s7 (by decide)
    (subtractMask (subtractSnapshot values 1) (subtractSnapshot values 3)) rfl
  have a0 := state.snapshots.load frame root layout 0 (by decide) body
  have a2 := state.snapshots.load frame root layout 2 (by decide) body
  have b1 := s5.snapshots.load frame root layout 1 (by decide) body
  have b3 := s5.snapshots.load frame root layout 3 (by decide) body
  have c0 := s6.snapshots.load frame root layout 0 (by decide) body
  have c2 := s6.snapshots.load frame root layout 2 (by decide) body
  have d1 := s7.snapshots.load frame root layout 1 (by decide) body
  have d3 := s7.snapshots.load frame root layout 3 (by decide) body
  cil_contract_steps [found, code, a0, a2, b1, b3, c0, c2, d1, d3, st4, st5, st6, st7,
    subtractMask, intrinsic_sub128, intrinsic_lt128] until continuation m7 s8

/-- Branch on the actual coalesced propagation test without writing memory. -/
theorem subtract_decision_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 63 subtractDecisionCode)
    (memory : Memory) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value) (values : Fin 4 → BitVec 128)
    (snapshots : VectorSnapshots memory slots (subtractSnapshot values) 10)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if subtractPropagation values = BitVec.ofNat 128 0 then 119 else 77)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 63 args frame [] memory = .ok (result, returned) ∧
        post result returned := by
  have a4 := snapshots.load frame root layout 4 (by decide) body
  have a5 := snapshots.load frame root layout 5 (by decide) body
  have a8 := snapshots.load frame root layout 8 (by decide) body
  have a9 := snapshots.load frame root layout 9 (by decide) body
  cil_contract_steps 13 [found, code, a4, a5, a8, a9, intrinsic_zero128, intrinsic_eq128,
    intrinsic_and128, intrinsic_or128, intrinsic_equal_all128]
  change ∃ fuel result returned, run program fuel method 76 args frame [.scalar (.i32
    (if subtractPropagation values == BitVec.ofNat 128 0 then 1 else 0))] memory = _ ∧ _
  by_cases zero : subtractPropagation values = BitVec.ofNat 128 0
  all_goals
    simp only [beq_iff_eq, zero, ↓reduceIte] at continuation ⊢
    cil_contract_steps [found, code] until continuation

end UInt256Proof.Subtract.Profile
