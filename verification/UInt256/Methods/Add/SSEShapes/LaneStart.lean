import UInt256.Methods.Add.SSEShapes.Helper

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- Entry prefix that loads the right upper half first and keeps the halves in locals 2, 3, 4, 1. -/
def lanesPrefix : List CIL.Op := [
  .arg 0,
  .memory .asRef,
  .memory .asRef,
  .arg 1,
  .memory .asRef,
  .memory .asRef,
  .setLocal 0,
  .local 0,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 1,
  .dup,
  .memory .load128,
  .setLocal 2,
  .local 0,
  .memory .load128,
  .setLocal 3,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 4,
  .local 2,
  .local 3,
  .intrinsic (.vector (.add64 128)) 2,
  .local 4,
  .local 1,
  .intrinsic (.vector (.add64 128)) 2,
  .setLocal 5,
  .dup,
  .local 2,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 6,
  .local 5,
  .local 4,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 7]

/-- Spec index of the private home for one input half. -/
def lanesLocal (right upper : Bool) : Nat :=
  if right then (if upper then 0 else 2) else (if upper then 3 else 1)

/-- Instruction index of the load for one input half. -/
def lanesLoad (right upper : Bool) : Nat :=
  if right then (if upper then 10 else 16) else (if upper then 20 else 13)

/-- Form both input references, save the right one in the root, and leave the left one on the stack. -/
theorem lanes_reference_prefix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (memory : Memory) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (initial : Option ManagedReference)
    (layout : frame.locals = .root initial :: slots) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (leftFormed : form memory left = .ok left)
    (rightFormed : form memory right = .ok right)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method 7 args (vector128SavedFrame frame slots right)
        [.reference (.address left)] memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] memory = .ok (result, returned) ∧
      post result returned := by

  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, lanesPrefix]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, leftArg, rightArg, checkedValue, formValue, leftFormed, rightFormed,
           staticInstruction, memoryInstruction, storeLocal, layout, vector128SavedFrame,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Reload the saved right reference above the left one, offsetting it for the upper half. -/
theorem lanes_right_reference (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (memory : Memory) (inputs outputs : List Reference)
    (right : Reference) (frame : Frame) (args rest : List Value)
    (slot : frame.locals[0]? = some (.root (some (.address right))))
    (call : CallingConditions program memory inputs outputs)
    (member : right ∈ inputs) (upper : Bool) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if upper then 10 else 16) args frame
        (.reference (.address { right with offset := right.offset + 16 * (if upper then 1 else 0) }) :: rest) memory =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (if upper then 7 else 15) args frame rest memory =
        .ok (result, returned) ∧ post result returned := by
  have formed := call.input_formed member
  have advanced := call.input_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at advanced

  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.mul_zero,
    Nat.mul_one, Nat.add_zero] at continuation ⊢
  all_goals
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by simp [code, lanesPrefix]; rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, slot, loadLocal, formValue, formed, staticInstruction, memoryInstruction,
             CIL.offsetValue, referenceAt, advanced, checkedAt, Except.mapError,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Duplicate the left reference before its lower-half load. -/
theorem lanes_left_dup (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (memory : Memory) (left : Reference) (frame : Frame) (args : List Value) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method 13 args frame [.reference (.address left), .reference (.address left)] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 12 args frame [.reference (.address left)] memory =
        .ok (result, returned) ∧ post result returned := by
  apply run_next_exists post found (by simp [code, lanesPrefix]; rfl) _ continuation
  simp (config := { implicitDefEqProofs := false })
    [step, instruction, pureArity, staticInstruction, memoryInstruction, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Offset the left reference to its upper half within the live input allocation. -/
theorem lanes_left_upper (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (memory : Memory) (inputs outputs : List Reference)
    (left : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program memory inputs outputs)
    (member : left ∈ inputs) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method 20 args frame
        [.reference (.address { left with offset := left.offset + 16 })] memory =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 18 args frame [.reference (.address left)] memory =
        .ok (result, returned) ∧ post result returned := by
  have advanced := call.input_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at advanced

  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, lanesPrefix]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, staticInstruction, memoryInstruction, CIL.offsetValue, referenceAt, advanced,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms lanes_reference_prefix
#print axioms lanes_right_reference
#print axioms lanes_left_dup
#print axioms lanes_left_upper
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- Each half-load/private-store pair captures initial caller bytes in its permuted home. -/
theorem lanes_operand (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstFour : ∀ i : Fin 4, specs[i.val]? = some vector128ZeroSpec)
    (original entered current : Memory)
    (inputs outputs : List Reference) (input : Reference) (frame : Frame)
    (root : LocalSlot) (slots : List LocalSlot) (args rest : List Value)
    (layout : frame.locals = root :: slots)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : input ∈ inputs) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (preserved : MemoryBelow original.nextIdentity original current)
    (authority : AccessBelow entered.nextIdentity entered current)
    (right upper : Bool)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[lanesLocal right upper + 1]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok
        (numberBytes (inputHalf original input (if upper then 1 else 0)).toNat 16) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (inputHalf original input (if upper then 1 else 0)).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (lanesLoad right upper + 2)
          args frame rest after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (lanesLoad right upper) args frame
        (.reference (.address { input with offset := input.offset + 16 * (if upper then 1 else 0) }) :: rest)
        current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[lanesLocal right upper]? = some vector128ZeroSpec := by
    exact firstFour ⟨lanesLocal right upper, by cases right <;> cases upper <;> decide⟩
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs original.nextIdentity entered current inputs outputs frame root slots
      layout currentCall enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (inputHalf original input (if upper then 1 else 0)))
      (inputHalf original input (if upper then 1 else 0)).toNat rfl
  have done := continuation reference after slot loaded (preserved.trans retained) afterCall afterAuthority written
  have reading := vector128_input_load program original current inputs outputs input
    (if upper then 1 else 0) call currentCall member preserved

  cases right <;> cases upper <;>
    simp only [lanesLoad, lanesLocal, Bool.false_eq_true, ite_false, ite_true,
      Fin.val_zero, Fin.val_one] at stored reading done ⊢
  all_goals
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at reading
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, lanesPrefix]; rfl)
         first
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, staticInstruction, memoryInstruction, reading, checkedAt, Except.mapError,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms lanes_operand
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- Save all four initial input halves in their permuted homes. -/
theorem lanes_inputs (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstFour : ∀ i : Fin 4, specs[i.val]? = some vector128ZeroSpec)
    (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ r1 l0 r0 l1 after,
      slots[0]? = some (.bytes .vector128 r1) →
      slots[1]? = some (.bytes .vector128 l0) →
      slots[2]? = some (.bytes .vector128 r0) →
      slots[3]? = some (.bytes .vector128 l1) →
      read after r1 16 1 = .ok (numberBytes (inputHalf original right 1).toNat 16) →
      read after l0 16 1 = .ok (numberBytes (inputHalf original left 0).toNat 16) →
      read after r0 16 1 = .ok (numberBytes (inputHalf original right 0).toNat 16) →
      read after l1 16 1 = .ok (numberBytes (inputHalf original left 1).toNat 16) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 22 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have authority : AccessBelow entered.nextIdentity entered entered := (MemoryBelow.refl _ _).accessBelow
  let saved := vector128SavedFrame frame slots right
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have savedRoot : saved.locals[0]? = some (.root (some (.address right))) := rfl
  apply lanes_reference_prefix program body method found tail code entered left right frame slots (some .null) layout args leftArg rightArg
    (enteredCall.input_formed leftMember) (enteredCall.input_formed rightMember) post
  apply lanes_right_reference program body method found tail code entered inputs outputs right saved args
    [.reference (.address left)] savedRoot enteredCall rightMember true post
  apply lanes_operand program body method specs found tail code firstFour original entered entered inputs outputs right saved
    (.root (some (.address right))) slots args [.reference (.address left)] savedLayout
    call enteredCall rightMember enteredCall.1.1 homes preserved authority true true post
  intro r1 m0 s0 read0 p0 c0 a0 w0
  apply lanes_left_dup program body method found tail code m0 left saved args post
  apply lanes_operand program body method specs found tail code firstFour original entered m0 inputs outputs left saved
    (.root (some (.address right))) slots args [.reference (.address left)] savedLayout
    call c0 leftMember enteredCall.1.1 homes p0 a0 false false post
  intro l0 m1 s1 read1 p1 c1 a1 w1
  apply lanes_right_reference program body method found tail code m1 inputs outputs right saved args
    [.reference (.address left)] savedRoot c1 rightMember false post
  apply lanes_operand program body method specs found tail code firstFour original entered m1 inputs outputs right saved
    (.root (some (.address right))) slots args [.reference (.address left)] savedLayout
    call c1 rightMember enteredCall.1.1 homes p1 a1 true false post
  intro r0 m2 s2 read2 p2 c2 a2 w2
  apply lanes_left_upper program body method found tail code m2 inputs outputs left saved args c2 leftMember post
  apply lanes_operand program body method specs found tail code firstFour original entered m2 inputs outputs left saved
    (.root (some (.address right))) slots args [] savedLayout
    call c2 leftMember enteredCall.1.1 homes p2 a2 false true post
  intro l1 after s3 read3 p3 c3 a3 w3
  simp only [lanesLocal, Bool.false_eq_true, ite_false, ite_true,
    Nat.reduceAdd, savedLayout, List.getElem?_cons_succ] at s0 s1 s2 s3
  have o01 := homes.ordered 0 1 .vector128 .vector128 r1 l0 (by decide) s0 s1
  have o02 := homes.ordered 0 2 .vector128 .vector128 r1 r0 (by decide) s0 s2
  have o03 := homes.ordered 0 3 .vector128 .vector128 r1 l1 (by decide) s0 s3
  have o12 := homes.ordered 1 2 .vector128 .vector128 l0 r0 (by decide) s1 s2
  have o13 := homes.ordered 1 3 .vector128 .vector128 l0 l1 (by decide) s1 s3
  have o23 := homes.ordered 2 3 .vector128 .vector128 r0 l1 (by decide) s2 s3
  have kept0 := write_preserves_disjoint_read w3
    (write_preserves_disjoint_read w2
      (write_preserves_disjoint_read w1 read0 (Or.inl (Nat.ne_of_lt o01)))
      (Or.inl (Nat.ne_of_lt o02))) (Or.inl (Nat.ne_of_lt o03))
  have kept1 := write_preserves_disjoint_read w3
    (write_preserves_disjoint_read w2 read1 (Or.inl (Nat.ne_of_lt o12))) (Or.inl (Nat.ne_of_lt o13))
  have kept2 := write_preserves_disjoint_read w3 read2 (Or.inl (Nat.ne_of_lt o23))
  exact continuation r1 l0 r0 l1 after s0 s1 s2 s3 kept0 kept1 kept2 read3 p3 c3 a3
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (Nat.le_trans (write_extends_allocations _ _ _ _ _ w2).next
          (write_extends_allocations _ _ _ _ _ w3).next)))

#print axioms lanes_inputs
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- Both lane sums from the permuted homes: lower sum on the stack, upper sum in its home. -/
theorem lanes_sum (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[5]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (halfSum (values 3) (values 0)).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfSum (values 3) (values 0)).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method 29 args frame
          [.scalar (.v128 (halfSum (values 1) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 4 vector128ZeroSpec (firstSeven 4)
      (.v128 (halfSum (values 3) (values 0))) (halfSum (values 3) (values 0)).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have load := fun (i : Fin 4) (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 (values i)) (values i).toNat rfl (located i) (readable i)

  repeat' first
    | exact done
    | (apply run_next_exists post found (by simp [code, lanesPrefix]; rfl)
       first
       | exact load 0 _ _
       | exact load 1 _ _
       | exact load 2 _ _
       | exact load 3 _ _
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_add128, halfSum, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Both carry-mask blocks compare a saved lane sum with its permuted left operand home. -/
theorem lanes_carry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high left : BitVec 128) (sumHome leftHome : Reference)
    (sumSlot : frame.locals[5]? = some (.bytes .vector128 sumHome))
    (leftSlot : frame.locals[if upper then 4 else 2]? = some (.bytes .vector128 leftHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (leftRead : read current leftHome 16 1 = .ok (numberBytes left.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if upper then 7 else 6]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (halfCarry (if upper then high else low) left).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfCarry (if upper then high else low) left).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (if upper then 37 else 33) args frame
          [.scalar (.v128 low)] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (if upper then 33 else 29) args frame
        [.scalar (.v128 low)] current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[if upper then 6 else 5]? = some vector128ZeroSpec := by
    cases upper <;> first | exact firstSeven 5 | exact firstSeven 6
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (halfCarry (if upper then high else low) left))
      (halfCarry (if upper then high else low) left).toNat rfl
  have actual : frame.locals[if upper then 7 else 6]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 left) left.toNat rfl leftSlot leftRead
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl sumSlot sumRead

  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadLeft done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, lanesPrefix]; rfl)
         first
         | exact loadLeft _ _
         | exact loadSum _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_lt128, halfCarry, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms lanes_sum
#print axioms lanes_carry
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety

/-- Compose the permuted lane sums and both mask stores. -/
theorem lanes_prepare (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ sum lowMask highMask after,
      slots[4]? = some (.bytes .vector128 sum) →
      slots[5]? = some (.bytes .vector128 lowMask) →
      slots[6]? = some (.bytes .vector128 highMask) →
      read after sum 16 1 = .ok (numberBytes (halfSum (values 3) (values 0)).toNat 16) →
      read after lowMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 1) (values 2)) (values 1)).toNat 16) →
      read after highMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 3) (values 0)) (values 3)).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 37 args frame
          [.scalar (.v128 (halfSum (values 1) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actual : ∀ i : Fin 4, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)) := by
    intro i
    simpa [layout] using located i
  apply lanes_sum program body method specs found tail code firstSeven boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority locations values actual readable post
  intro sum m0 sumSlot sumRead p0 c0 a0 w0
  have sumTail : slots[4]? = some (.bytes .vector128 sum) := by simpa [layout] using sumSlot
  have reads0 : ∀ i, read m0 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered current m0 boundary slots homes i.val 4 i.isLt
      (locations i) sum (located i) sumTail _ _ w0 (readable i)
  apply lanes_carry program body method specs found tail code firstSeven boundary entered m0 inputs outputs frame root slots layout args c0
    enteredWF homes a0 false (halfSum (values 1) (values 2)) (halfSum (values 3) (values 0))
    (values 1) sum (locations 1) sumSlot (actual 1) sumRead (reads0 1) post
  intro lowMask m1 lowSlot lowRead p1 c1 a1 w1
  have lowTail : slots[5]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowSlot
  have sumRead1 := vector128_prior_read specs entered m0 m1 boundary slots homes 4 5 (by decide)
    sum lowMask sumTail lowTail _ _ w1 sumRead
  have reads1 : ∀ i, read m1 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered m0 m1 boundary slots homes i.val 5 (by omega)
      (locations i) lowMask (located i) lowTail _ _ w1 (reads0 i)
  apply lanes_carry program body method specs found tail code firstSeven boundary entered m1 inputs outputs frame root slots layout args c1
    enteredWF homes a1 true (halfSum (values 1) (values 2)) (halfSum (values 3) (values 0))
    (values 3) sum (locations 3) sumSlot (actual 3) sumRead1 (reads1 3) post
  intro highMask after highSlot highRead p2 c2 a2 w2
  have highTail : slots[6]? = some (.bytes .vector128 highMask) := by simpa [layout] using highSlot
  have sumFinal := vector128_prior_read specs entered m1 after boundary slots homes 4 6 (by decide)
    sum highMask sumTail highTail _ _ w2 sumRead1
  have lowFinal := vector128_prior_read specs entered m1 after boundary slots homes 5 6 (by decide)
    lowMask highMask lowTail highTail _ _ w2 lowRead
  exact continuation sum lowMask highMask after sumTail lowTail highTail sumFinal lowFinal highRead
    (p0.trans (p1.trans p2)) c2 a2
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (write_extends_allocations _ _ _ _ _ w2).next))

/-- Initial halves in the permuted home order: right upper, left lower, right lower, left upper. -/
def lanesHalves (memory : Memory) (left right : Reference) (i : Fin 4) : BitVec 128 :=
  if i = 0 then inputHalf memory right 1 else if i = 1 then inputHalf memory left 0
  else if i = 2 then inputHalf memory right 0 else inputHalf memory left 1

/-- The permuted-home start satisfies the start contract. -/
theorem lanes_start (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec) :
    StartContract program body method specs := by
  intro original entered inputs outputs left right frame slots args call setup layout homes leftMember rightMember
    leftArg rightArg post continuation
  apply lanes_inputs program body method specs found tail code (fun i => firstSeven ⟨i.val, by omega⟩)
    original entered inputs outputs left right frame slots args call setup layout homes leftMember rightMember
    leftArg rightArg post
  intro r1 l0 r0 l1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority next
  let locations : Fin 4 → Reference := fun i =>
    if i = 0 then r1 else if i = 1 then l0 else if i = 2 then r0 else l1
  have located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simpa [locations] using (by assumption)
  have readable : ∀ i, read current (locations i) 16 1 =
      .ok (numberBytes (lanesHalves original left right i).toNat 16) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simpa [locations, lanesHalves] using (by assumption)
  apply lanes_prepare program body method specs found tail code firstSeven original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args
    currentCall (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    locations (lanesHalves original left right) located readable post
  intro sum lowMask highMask after sumSlot lowSlot highSlot sumRead lowRead highRead kept afterCall afterAuthority advanced
  exact continuation sum lowMask highMask after sumSlot lowSlot highSlot sumRead lowRead highRead
    (preserved.trans kept) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms lanes_prepare
#print axioms lanes_start
end UInt256Proof.Add.SSEShapes
