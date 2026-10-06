import UInt256.Methods.Add.Vector128ARMScalarSetup

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

def armScalarUpper (memory : Memory) (input : Reference) : BitVec 64 :=
  inputLimb memory input 1 ||| inputLimb memory input 2 ||| inputLimb memory input 3

def armScalarTarget (memory : Memory) (left right : Reference) : Nat :=
  if armScalarUpper memory right = BitVec.ofNat 64 0 then 36
  else if armScalarUpper memory left = BitVec.ofNat 64 0 then 31 else 25

/-- Both operand tests are followed in order, preserving all memory and locals.
    A zero upper part selects a small helper; otherwise execution reaches vector dispatch. -/
theorem arm_scalar_decisions (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (inputs outputs : List Reference)
    (left right : Reference) (call : CallingConditions Extracted.program memory inputs outputs)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (armScalarTarget memory left right)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 7 args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  unfold armScalarTarget at continuation
  apply arm_scalar_upper_loads enabled false memory frame args inputs outputs right
    call rightMember rightArg post
  apply arm_scalar_upper_branch enabled false memory frame args (armScalarUpper memory right) post
  by_cases small : armScalarUpper memory right = BitVec.ofNat 64 0
  · simpa only [small, Bool.false_eq_true, ite_false, ite_true] using continuation
  · simp only [small, ite_false, Bool.false_eq_true] at *
    apply arm_scalar_upper_loads enabled true memory frame args inputs outputs left
      call leftMember leftArg post
    apply arm_scalar_upper_branch enabled true memory frame args (armScalarUpper memory left) post
    simpa only [small,  ite_false, ite_true] using continuation

/-- Actual entry through all operand decisions, carrying initialized private data
    and the caller footprint into every selected continuation. -/
theorem arm_scalar_dispatch_prefix (enabled : Extracted.profile.advSimd = true)
    (boundary : Nat) (entered : Memory) (inputs outputs : List Reference)
    (frame : Frame) (args : List Value) (left right : Reference)
    (call : CallingConditions Extracted.program entered inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered boundary scalarLocalSpecs frame.locals)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ home after,
      frame.locals[8]? = some (.bytes .word64 home) →
      read after home 8 1 = .ok (numberBytes (inputLimb entered right 0).toNat 8) →
      MemoryBelow boundary entered after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarIndex (armScalarTarget after left right) args
          (armScalarSavedFrame frame left) [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 0 args frame [] entered =
        .ok (final, returned) ∧ post final returned := by
  apply arm_scalar_initial_prefix enabled boundary entered inputs outputs frame args left right
    call enteredWF homes leftMember rightMember leftArg rightArg post
  intro home after slot loaded preserved afterCall authority
  exact arm_scalar_decisions enabled after (armScalarSavedFrame frame left) args inputs outputs
    left right afterCall leftMember rightMember leftArg rightArg post
    (continuation home after slot loaded preserved afterCall authority)

#print axioms arm_scalar_decisions
#print axioms arm_scalar_dispatch_prefix
end UInt256Proof.Add.Safety
