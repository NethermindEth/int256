import UInt256.Safety.RegionSteps
import UInt256.Safety.Calling

namespace UInt256Proof.Transport
open CIL.Safety UInt256Model.Safety

/-- Every checked step of the body continues in place or returns; it never calls or constructs. -/
def CallFree (body : CIL.Method) : Prop :=
  ∀ op ∈ body.code, ∀ pc args frame stack memory action,
    step body op pc args frame stack memory = .ok action → FlowResult 0 (fun _ => False) action

/-- The relocated suffix of the replaced method and the whole call-free storage callee. -/
def suffixRegion (index storage lower method pc : Nat) : Prop :=
  method = storage ∨ method = index ∧ lower ≤ pc

def suffixMap (index : Nat) (f : Nat → Nat) (method pc : Nat) : Nat :=
  if method = index then f pc else pc

/-- Replacing one method by a body whose suffix is the source suffix at relocated PCs
    preserves every checked step reachable from that suffix. -/
theorem suffix_correspondence (program : CIL.Program) (index storage lower : Nat) (f : Nat → Nat)
    (source target storageBody : CIL.Method) (distinct : index ≠ storage)
    (found : program[index]? = some target) (storageFound : program[storage]? = some storageBody)
    (callFree : CallFree storageBody)
    (frames : ∀ args memory, enterFrame target args memory = enterFrame source args memory)
    (steps : ∀ op pc args frame stack memory,
      step target op pc args frame stack memory = step source op pc args frame stack memory)
    (successor : ∀ pc, lower ≤ pc → f (pc + 1) = f pc + 1)
    (supported : ∀ pc op, lower ≤ pc → source.code[pc]? = some op →
      Supported op ∧ FlowInput lower (· = storage) op)
    (lookup : ∀ pc, lower ≤ pc → target.code[f pc]? = (source.code[pc]?).map (relocateOp f)) :
    Correspondence (program.set index source) program (suffixRegion index storage lower) (suffixMap index f) := by
  have indexBound : index < program.length := (List.getElem?_eq_some_iff.mp found).choose
  constructor
  · intro method body sourceFound
    by_cases equal : method = index
    · subst method
      rw [List.getElem?_set_self indexBound] at sourceFound
      cases sourceFound
      exact ⟨target, found, frames⟩
    · rw [List.getElem?_set_ne (Ne.symm equal)] at sourceFound
      exact ⟨body, sourceFound, fun _ _ => rfl⟩
  · intro method pc body op args frame stack memory action inside sourceFound opcode executed
    rcases inside with storageCase | ⟨indexCase, lower'⟩
    · subst method
      rw [List.getElem?_set_ne distinct, storageFound] at sourceFound
      cases sourceFound
      have flow := callFree op (List.mem_of_getElem? opcode) pc args frame stack memory action executed
      refine ⟨storageBody, op, storageFound, ?_, ?_, ?_⟩
      · simpa [suffixMap, Ne.symm distinct] using opcode
      · cases action <;> simpa [suffixMap, Ne.symm distinct, relocateAction] using executed
      · cases action <;> simp_all [closedAction, FlowResult, suffixRegion]
    · subst method
      rw [List.getElem?_set_self indexBound] at sourceFound
      cases sourceFound
      obtain ⟨allowed, targets⟩ := supported pc op lower' opcode
      have flow := supported_flow _ op allowed pc args frame stack memory action lower (· = storage) (by omega)
        targets executed
      refine ⟨target, relocateOp f op, found, ?_, ?_, ?_⟩
      · simpa [suffixMap, opcode] using lookup pc lower'
      · rw [steps]
        simp only [suffixMap, ite_true]
        rw [supported_relocate _ op allowed f pc args frame stack memory (successor pc lower'), executed]
        cases action <;> simp [Except.map, relocateAction, suffixMap]
      · have next := successor pc lower'
        cases action <;> simp_all [closedAction, FlowResult, suffixRegion, suffixMap]
        omega

/-- A replaced method with the same static sites leaves the program's static world unchanged. -/
theorem set_static (program : CIL.Program) (index : Nat) (source target : CIL.Method)
    (found : program[index]? = some target) (same : source.staticSites = target.staticSites) :
    programStaticDescriptors (program.set index source) = programStaticDescriptors program := by
  induction program generalizing index with
  | nil => simp at found
  | cons body rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst body
      simp only [List.set_cons_zero, programStaticDescriptors, List.flatMap_cons, same]
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa only [List.set_cons_succ, programStaticDescriptors, List.flatMap_cons] using
        congrArg (body.staticSites.map Prod.snd ++ ·) (ih index found)

theorem set_calling {program : CIL.Program} {index : Nat} {source target : CIL.Method}
    (found : program[index]? = some target) (same : source.staticSites = target.staticSites)
    {memory : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) :
    CallingConditions (program.set index source) memory inputs outputs := by
  refine ⟨call.1, ?_⟩
  simpa only [set_static program index source target found same] using call.2

#print axioms suffix_correspondence
#print axioms set_calling
end UInt256Proof.Transport
