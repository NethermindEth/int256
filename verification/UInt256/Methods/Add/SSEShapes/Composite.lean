import UInt256.Methods.Add.SSEShapes.Entry

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- From helper entry to the fast/repair branch: every saved vector from the upper sum on is tied to the initial inputs. -/
theorem shaped_dispatch (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (layout : Layout) (shaped : Shaped body layout)
    (start : StartContract program body method specs)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse2 : body.profile.sse2 = true) (ssse3 : body.profile.ssse3 = true) (disabled : body.profile.advSimd = false)
    (mergeFound : ∀ index, layout.merge = some index → program[index]? = some (mergeBody body.profile))
    (original entered : Memory) (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (frameLayout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after conditionHome,
      slots[13]? = some (.bytes .vector128 conditionHome) →
      read after conditionHome 16 1 = .ok (numberBytes
        (vector128BranchValue original left right 11 ||| vector128BranchValue original left right 12).toNat 16) →
      (∀ i : Fin 13, 4 ≤ i.val → ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      MemoryBelow original.nextIdentity original after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method
          (if (vector128BranchValue original left right 11 ||| vector128BranchValue original left right 12) =
            BitVec.ofNat 128 0 then layout.fast else layout.join + 5)
          args (vector128SavedFrame frame slots right) [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered = .ok (result, returned) ∧ post result returned := by
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply start original entered inputs outputs left right frame slots args call setup frameLayout homes leftMember
    rightMember leftArg rightArg post
  intro sum lowMask highMask m0 sumSlot lowSlot highSlot sumRead lowRead highRead p0 c0 a0 n0
  obtain ⟨gL, gT, gLen, gCode⟩ := shaped.incomingGuard
  apply guard_skip program body method found gL gT 37 gLen _ _ gCode disabled args _ _ m0 post
  obtain ⟨iL, iT, iLen, iCode⟩ := shaped.incoming
  apply incoming_pair program body method specs found iT iL layout.incoming iLen iCode sse2 ssse3
    ⟨firstFourteen 7, firstFourteen 8⟩ original.nextIdentity entered m0 inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c0 enteredWF homes a0
    (vector128SnapshotValue original left right 5) (vector128SnapshotValue original left right 6)
    [.scalar (.v128 (halfSum (inputHalf original left 0) (inputHalf original right 0)))]
    lowMask highMask lowSlot highSlot lowRead highRead post
  intro lowIncoming highIncoming m1 liSlot hiSlot liRead hiRead kept1 p1 c1 a1 n1
  obtain ⟨cL, cT, cLen, cCode⟩ := shaped.correction
  apply correction_pair program body method specs found cL cT (layout.incoming + 12) cLen cCode
    ⟨firstFourteen 9, firstFourteen 10⟩ original.nextIdentity entered m1 inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c1 enteredWF homes a1
    (halfSum (inputHalf original left 0) (inputHalf original right 0))
    (vector128SnapshotValue original left right 4)
    (vector128SnapshotValue original left right 7) (vector128SnapshotValue original left right 8)
    sum lowIncoming highIncoming sumSlot liSlot hiSlot
    (kept1 4 (by decide) sum _ sumSlot sumRead) liRead hiRead post
  intro lowResult highResult m2 lrSlot hrSlot lrRead hrRead kept2 p2 c2 a2 n2
  obtain ⟨eL, eT, eLen, eCode⟩ := shaped.early
  have earlyStart : layout.incoming + 12 + 7 = layout.incoming + 19 := by omega
  rw [earlyStart]
  apply early_skip program body method found eL eT (layout.incoming + 19) eLen _ _ eCode disabled m2 output
    (vector128SavedFrame frame slots right) args outputArg (c2.output_formed outputMember) post
  obtain ⟨pL, pT, pLen, pCode⟩ := shaped.propagation
  apply propagation_pair program body method specs found pL pT layout.propagation pLen pCode
    ⟨firstFourteen 11, firstFourteen 12⟩ original.nextIdentity entered m2 inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c2 enteredWF homes a2
    (vector128SnapshotValue original left right 9) (vector128SnapshotValue original left right 10)
    (vector128SnapshotValue original left right 7) (vector128SnapshotValue original left right 8)
    lowResult highResult lowIncoming highIncoming lrSlot hrSlot liSlot hiSlot lrRead hrRead
    (kept2 7 (by decide) _ _ liSlot liRead) (kept2 8 (by decide) _ _ hiSlot hiRead) post
  intro lowProp highProp m3 lpSlot hpSlot lpRead hpRead kept3 p3 c3 a3 n3
  obtain ⟨dL, dT, dLen, dCode⟩ := shaped.decisionGuard
  apply guard_skip program body method found dL dT (layout.propagation + 12) dLen _ _ dCode disabled args _ _ m3 post
  obtain ⟨kL, kT, kLen, kCode⟩ := shaped.combine
  obtain ⟨jL, jT, jLen, jCode⟩ := shaped.join
  have actualLow : (vector128SavedFrame frame slots right).locals[12]? = some (.bytes .vector128 lowProp) := lpSlot
  have actualHigh : (vector128SavedFrame frame slots right).locals[13]? = some (.bytes .vector128 highProp) := hpSlot
  apply combine_checked program body method found kL kT layout.combine kLen layout.merge layout.join layout.fast kCode
    jL jT jLen jCode mergeFound specs (firstFourteen 13) original.nextIdentity entered m3 inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c3 enteredWF homes a3
    (vector128BranchValue original left right 11) (vector128BranchValue original left right 12)
    lowProp highProp actualLow actualHigh lpRead hpRead post
  intro conditionHome m4 conditionSlot conditionRead p4 c4 a4 w4
  apply join_branch program body method found jL jT layout.join jLen layout.fast jCode m4
    (vector128SavedFrame frame slots right) args conditionHome _ conditionSlot conditionRead post
  have conditionTail : slots[13]? = some (.bytes .vector128 conditionHome) := conditionSlot
  have atThree : ∀ i : Fin 13, 4 ≤ i.val → ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read m3 reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16) := by
    intro i lower
    have cases : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨sum, sumSlot, kept3 4 (by decide) _ _ sumSlot (kept2 4 (by decide) _ _ sumSlot
        (kept1 4 (by decide) _ _ sumSlot sumRead))⟩
    · exact ⟨lowMask, lowSlot, kept3 5 (by decide) _ _ lowSlot (kept2 5 (by decide) _ _ lowSlot
        (kept1 5 (by decide) _ _ lowSlot lowRead))⟩
    · exact ⟨highMask, highSlot, kept3 6 (by decide) _ _ highSlot (kept2 6 (by decide) _ _ highSlot
        (kept1 6 (by decide) _ _ highSlot highRead))⟩
    · exact ⟨lowIncoming, liSlot, kept3 7 (by decide) _ _ liSlot (kept2 7 (by decide) _ _ liSlot liRead)⟩
    · exact ⟨highIncoming, hiSlot, kept3 8 (by decide) _ _ hiSlot (kept2 8 (by decide) _ _ hiSlot hiRead)⟩
    · exact ⟨lowResult, lrSlot, kept3 9 (by decide) _ _ lrSlot lrRead⟩
    · exact ⟨highResult, hrSlot, kept3 10 (by decide) _ _ hrSlot hrRead⟩
    · exact ⟨lowProp, lpSlot, lpRead⟩
    · exact ⟨highProp, hpSlot, hpRead⟩
  have retained : ∀ i : Fin 13, 4 ≤ i.val → ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read m4 reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16) := by
    intro i lower
    obtain ⟨reference, slot, loaded⟩ := atThree i lower
    exact ⟨reference, slot, vector128_prior_read specs entered m3 m4 original.nextIdentity slots homes
      i.val 13 i.isLt reference conditionHome slot conditionTail _ _ w4 loaded⟩
  have conditionValue := continuation m4 conditionHome conditionTail conditionRead retained c4 a4
    (p0.trans (p1.trans (p2.trans (p3.trans p4))))
    (Nat.le_trans n0 (Nat.le_trans n1 (Nat.le_trans n2 (Nat.le_trans n3
      (write_extends_allocations _ _ _ _ _ w4).next))))
  exact conditionValue

#print axioms shaped_dispatch

/-- Both helper branches from entry: modular sum of the initial operands, checked return, caller bytes kept. -/
theorem shaped_entry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (layout : Layout) (shaped : Shaped body layout)
    (start : StartContract program body method specs)
    (repair : RepairContract program method specs layout.repair)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse2 : body.profile.sse2 = true) (ssse3 : body.profile.ssse3 = true) (disabled : body.profile.advSimd = false)
    (mergeFound : ∀ index, layout.merge = some index → program[index]? = some (mergeBody body.profile))
    (returns : body.returnsValue = true) (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame body args original = .ok (frame, entered))
    (frameLayout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧
        CIL.NarrowKind.unsigned8.extend returnedFlag = returnedFlag ∧
        (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
          if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧
      CIL.NarrowKind.unsigned8.extend returnedFlag = returnedFlag ∧
      (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
        if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
    inputValue final output = inputValue original left + inputValue original right ∧
    access final output 32 1 true = .ok () ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = original.cells id offset)
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ (vector128SavedFrame frame slots right).owned, original.nextIdentity ≤ id :=
    fun id member => (fresh.2 id member).1
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply shaped_dispatch program body method specs found layout shaped start firstFourteen sse2 ssse3 disabled mergeFound
    original entered [left, right] [output] left right output frame slots args call setup frameLayout homes
    (by simp) (by simp) (by simp) leftArg rightArg outputArg post
  intro current conditionHome _ _ retained currentCall authority preserved _
  by_cases fast : (vector128BranchValue original left right 11 ||| vector128BranchValue original left right 12) =
      BitVec.ofNat 128 0
  · simp only [fast, ite_true]
    have selected : selectedPropagation128 false flag (vector128BranchValue original left right 11)
        (vector128BranchValue original left right 12) = BitVec.ofNat 128 0 := by
      simpa [selectedPropagation128] using fast
    obtain ⟨lowHome, lowSlot, lowRead⟩ := retained 9 (by decide)
    obtain ⟨highHome, highSlot, highRead⟩ := retained 10 (by decide)
    obtain ⟨carryHome, carrySlot, carryRead⟩ := retained 6 (by decide)
    obtain ⟨fL, fT, fLen, fCode⟩ := shaped.fast
    obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
      fast_result program body method found fL fT layout.fast fLen fCode disabled returns original entered current
        [left, right] [output] output (vector128SavedFrame frame slots right) args call currentCall (by simp) authority
        outputArg (vector128SnapshotValue original left right 9) (vector128SnapshotValue original left right 10)
        lowHome highHome lowSlot highSlot (homes.home_bound 10 .vector128 highHome highSlot)
        lowRead highRead carryHome (vector128BranchValue original left right 6) carrySlot
        (homes.home_bound 6 .vector128 carryHome carrySlot) carryRead left right flag rfl rfl selected owned
    exact ⟨fuel, final, returned, executed,
      ⟨_, scalar, (by split <;> rfl), fun reporting =>
        vector128_snapshot_fast_flag false original left right flag reporting selected⟩,
      result, writable, fun id offset old untouched =>
        (outside id offset old untouched).trans (preserved.cells id old offset)⟩
  · simp only [fast, ite_false]
    obtain ⟨rL, rT, rLen, rCode⟩ := shaped.repairGuard
    apply guard_skip program body method found rL rT (layout.join + 5) rLen _ _ rCode disabled args [] _ current post
    obtain ⟨fuel, final, values, executed, result⟩ := repair original entered current
      (vector128SavedFrame frame slots right) slots left right output args rfl call currentCall preserved homes
      enteredWF authority leftArg rightArg outputArg owned
    exact ⟨fuel, final, values, executed,
      ⟨_, result.flag, (by unfold UInt256Proof.Safety.addOverflow; split <;> rfl), fun _ => rfl⟩,
      result.value, result.writable, fun id offset bound untouched => result.footprint id bound offset untouched⟩

/-- Checked invocation of a shaped SSE helper body. -/
theorem checked_shaped_contract (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (layout : Layout) (shaped : Shaped body layout)
    (start : StartContract program body method specs)
    (repair : RepairContract program method specs layout.repair)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse2 : body.profile.sse2 = true) (ssse3 : body.profile.ssse3 = true) (disabled : body.profile.advSimd = false)
    (mergeFound : ∀ index, layout.merge = some index → program[index]? = some (mergeBody body.profile))
    (returns : body.returnsValue = true)
    (metadata : body.localKinds = .reference :: specs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: specs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (memory : Memory) (left right output : Reference) (flag : BitVec 32)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      CIL.NarrowKind.unsigned8.extend returned = returned ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, slots, setup, frameLayout, homes, _, _⟩ :=
    vector128_frame_setup body specs metadata vectors parameters memory args call.1.1
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, footprint⟩ :=
    shaped_entry program body method specs found layout shaped start repair firstFourteen sse2 ssse3 disabled mergeFound
      returns memory entered left right output frame slots args call setup frameLayout homes rfl rfl rfl flag
  obtain ⟨returnedValue, rfl, returnedFit, overflow⟩ := scalar
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returnedValue,
    certify_invocation program method body args memory frame entered
      fuel final [.scalar (.i32 returnedValue)] found checked setup live executed,
    result, returnedFit, overflow, writable, footprint⟩

#print axioms shaped_entry
#print axioms checked_shaped_contract

end UInt256Proof.Add.SSEShapes
