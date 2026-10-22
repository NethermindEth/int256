import UInt256.Safety.RegionTransport
import UInt256.Safety.Calling
import CIL.Safety.Embedding.Simulation

namespace UInt256Proof.Transport
open CIL.Safety UInt256Model.Safety

/-- Every checked step of the body continues in place or returns; it never calls or constructs. -/
def CallFree (body : CIL.Method) : Prop :=
  ∀ op ∈ body.code, ∀ pc args frame stack memory action,
    step body op pc args frame stack memory = .ok action → FlowResult 0 (fun _ => False) action

theorem CallFree.of_flow {body : CIL.Method} (flow : ∀ op ∈ body.code, FlowInput 0 (fun _ => False) op) :
    CallFree body := fun op member pc args frame stack memory action executed =>
  step_flow body op pc args frame stack memory action 0 _ (by omega) (flow op member) executed

/-- The relocated suffix of the replaced method and the whole call-free storage callee. -/
def suffixRegion (index storage lower method pc : Nat) : Prop :=
  method = storage ∨ method = index ∧ lower ≤ pc

def suffixMap (index : Nat) (f : Nat → Nat) (method pc : Nat) : Nat :=
  if method = index then f pc else pc

/-- Replacing one method by a body whose suffix is the source suffix relabeled at relocated PCs
    preserves every checked step reachable from that suffix. -/
theorem suffix_correspondence (program : CIL.Program) (index storage lower : Nat) (f : Nat → Nat)
    (source target storageBody : CIL.Method) (distinct : index ≠ storage)
    (found : program[index]? = some target) (storageFound : program[storage]? = some storageBody)
    (callFree : CallFree storageBody)
    (frames : ∀ args memory, enterFrame target args memory = enterFrame source args memory)
    (profile : target.profile = source.profile) (returnsValue : target.returnsValue = source.returnsValue)
    (statics : ∀ pc, lower ≤ pc → CIL.Embedding.staticAt target (f pc) = CIL.Embedding.staticAt source pc)
    (successor : ∀ pc, lower ≤ pc → f (pc + 1) = f pc + 1)
    (flow : ∀ pc op, lower ≤ pc → source.code[pc]? = some op → FlowInput lower (· = storage) op)
    (lookup : ∀ pc, lower ≤ pc → target.code[f pc]? = (source.code[pc]?).map (CIL.Op.relabel f)) :
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
      have result := callFree op (List.mem_of_getElem? opcode) pc args frame stack memory action executed
      refine ⟨storageBody, op, storageFound, ?_, ?_, ?_⟩
      · simpa [suffixMap, Ne.symm distinct] using opcode
      · cases action <;> simpa [suffixMap, Ne.symm distinct, FrameAction.relabel] using executed
      · cases action <;> simp_all [closedAction, FlowResult, suffixRegion]
    · subst method
      rw [List.getElem?_set_self indexBound] at sourceFound
      cases sourceFound
      have result := step_flow _ op pc args frame stack memory action lower (· = storage) (by omega)
        (flow pc op lower' opcode) executed
      refine ⟨target, op.relabel f, found, ?_, ?_, ?_⟩
      · simpa [suffixMap, opcode] using lookup pc lower'
      · rw [show suffixMap index f index = f from funext fun _ => ite_eq_left rfl]
        exact step_relabel op source target f pc (f pc) args frame stack memory action
          ⟨profile, returnsValue, statics pc lower', fun _ => successor pc lower'⟩ executed
      · have next := successor pc lower'
        cases action <;> simp_all [closedAction, FlowResult, suffixRegion, suffixMap]
        omega

/-- A replaced method with the same static sites keeps the caller's static-world condition. -/
theorem set_calling {program : CIL.Program} {index : Nat} {source target : CIL.Method}
    (found : program[index]? = some target) (same : source.staticSites = target.staticSites)
    {memory : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) :
    CallingConditions (program.set index source) memory inputs outputs := by
  refine ⟨call.1, ?_⟩
  rw [programStaticDescriptors_set program index source fun old present => by
    rw [found] at present; cases present; rw [same]]
  exact call.2

#print axioms suffix_correspondence
#print axioms set_calling
end UInt256Proof.Transport
