import UInt256.Safety.StepEquation
import UInt256.Safety.RegionTransport

namespace UInt256Proof.Transport
open CIL.Safety


theorem map_bind (input : Except ε α) (next : α → Except ε β) (mapping : β → γ) :
    (input.bind next).map mapping = input.bind (fun value => (next value).map mapping) := by
  cases input <;> rfl

theorem arg_relocate (body : CIL.Method) (index : Nat) (f : Nat → Nat) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (successor : f (pc + 1) = f pc + 1) :
    step body (.arg index) (f pc) args frame stack memory =
      (step body (.arg index) pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  delta step
  dsimp only
  cases args[index]? with
  | none => rfl
  | some value =>
    simp only [Bind.bind, map_bind, Pure.pure, Except.pure]
    congr 1
    funext checked
    simp [Except.map, relocateAction, successor]

theorem local_relocate (body : CIL.Method) (index : Nat) (f : Nat → Nat) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (successor : f (pc + 1) = f pc + 1) :
    step body (.local index) (f pc) args frame stack memory =
      (step body (.local index) pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  delta step
  dsimp only
  cases frame.locals[index]? with
  | none => rfl
  | some slot =>
    simp only [Bind.bind, map_bind, Pure.pure, Except.pure]
    congr 1
    funext loaded
    simp [Except.map, relocateAction, successor]

theorem setLocal_relocate (body : CIL.Method) (index : Nat) (f : Nat → Nat) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (successor : f (pc + 1) = f pc + 1) :
    step body (.setLocal index) (f pc) args frame stack memory =
      (step body (.setLocal index) pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  cases stack with
  | nil => rfl
  | cons value rest =>
    delta step
    dsimp only
    cases frame.locals[index]? with
    | none => rfl
    | some slot =>
      simp only [Bind.bind, map_bind, Pure.pure, Except.pure]
      congr 1
      funext stored
      rcases stored with ⟨slot, updated⟩
      simp [Except.map, relocateAction, successor]

theorem call_relocate (body : CIL.Method) (callee argc : Nat) (f : Nat → Nat) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) :
    step body (.call callee argc) (f pc) args frame stack memory =
      (step body (.call callee argc) pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  delta step
  dsimp only
  split
  · rfl
  · simp only [Bind.bind, map_bind, Pure.pure, Except.pure]
    congr 1

theorem return_relocate (body : CIL.Method) (f : Nat → Nat) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) :
    step body .ret (f pc) args frame stack memory =
      (step body .ret pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  delta step
  dsimp only
  split <;> split
  all_goals first | rfl | (cases stack.mapM (checkedValue memory) <;> rfl)

inductive MemoryOp : CIL.Op → Prop where
  | const32 (word : BitVec 32) : MemoryOp (.const32 word)
  | const64 (word : BitVec 64) : MemoryOp (.const64 word)
  | fieldAt (offset width : Nat) : MemoryOp (.fieldAt offset width)
  | initAggregate (size : Nat) : MemoryOp (.initAggregate size)

theorem memory_form (body : CIL.Method) (op : CIL.Op) (allowed : MemoryOp op) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) (pc : Nat) : step body op pc args frame stack memory = do
    let (updated, values) ← instruction op stack memory
    return .next (pc + 1) values frame updated := by
  cases allowed <;> rfl

theorem memory_relocate (body : CIL.Method) (op : CIL.Op) (allowed : MemoryOp op)
    (f : Nat → Nat) (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (successor : f (pc + 1) = f pc + 1) :
    step body op (f pc) args frame stack memory =
      (step body op pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  have form := memory_form body op allowed args frame stack memory
  rw [form, form]
  simp only [Bind.bind, map_bind]
  congr 1
  funext outcome
  rcases outcome with ⟨updated, values⟩
  simp [Except.map, relocateAction, successor, Pure.pure, Except.pure]

inductive BinaryOp : CIL.Op → Prop where
  | band : BinaryOp .band
  | bor : BinaryOp .bor
  | sub : BinaryOp .sub
  | shl : BinaryOp .shl
  | shr : BinaryOp .shr
  | shrUn : BinaryOp .shrUn

def binaryStack (op : CIL.Op) : List CIL.Value → Option (List CIL.Value)
  | right :: left :: rest => (CIL.binary op left right).map (· :: rest)
  | _ => none

theorem binary_pure (op : CIL.Op) (allowed : BinaryOp op) (pc : Nat) (stack : List CIL.Value)
    (profile : CIL.FeatureProfile) :
    CIL.step op false pc [] 0 stack (fun _ => none) profile =
      (binaryStack op stack).map (fun values => CIL.Action.next (pc + 1) values (fun _ => none)) := by
  cases allowed <;> cases stack with
  | nil => rfl
  | cons right tail =>
    cases tail with
    | nil => rfl
    | cons left rest =>
      delta CIL.step
      dsimp only [binaryStack]
      cases CIL.binary _ left right <;> rfl

theorem binary_form (body : CIL.Method) (op : CIL.Op) (allowed : BinaryOp op) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) (pc : Nat) : step body op pc args frame stack memory =
    (if stack.length < 2 then .error .invalidState else do
      let values ← scalars (stack.take 2)
      let some result := binaryStack op values | .error .invalidState
      let checked ← (result.map Value.scalar).mapM (checkedValue memory)
      return .next (pc + 1) (checked ++ stack.drop 2) frame memory) := by
  have raw := binary_pure op allowed pc
  cases allowed <;> delta step <;> dsimp only [pureArity]
  all_goals split
  all_goals first
    | rfl
    | (congr 1; funext values; rw [raw]; cases binaryStack _ values <;> rfl)

theorem binary_relocate (body : CIL.Method) (op : CIL.Op) (allowed : BinaryOp op)
    (f : Nat → Nat) (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (successor : f (pc + 1) = f pc + 1) :
    step body op (f pc) args frame stack memory =
      (step body op pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  have arity : pureArity op = some 2 := by cases allowed <;> rfl
  have form := binary_form body op allowed args frame stack memory
  rw [form, form]
  split
  · rfl
  · simp only [Bind.bind, map_bind]
    congr 1
    funext values
    cases found : binaryStack op values with
    | none => rfl
    | some result =>
      simp only [map_bind, Pure.pure, Except.pure]
      congr 1
      funext checked
      simp [Except.map, relocateAction, successor]

inductive BranchKind where
  | ge | ult | ne | nonzero

def branchOp : BranchKind → Nat → CIL.Op
  | .ge, target => .bge target
  | .ult, target => .bltu target
  | .ne, target => .bne target
  | .nonzero, target => .brnonzero target

def branchArity : BranchKind → Nat | .nonzero => 1 | _ => 2

def branchTest : BranchKind → List CIL.Value → Option (Bool × List CIL.Value)
  | .nonzero, value :: rest => (CIL.truth value).map (·, rest)
  | .ge, .i32 b :: .i32 a :: rest => some (decide (b.toInt ≤ a.toInt), rest)
  | .ge, .i64 b :: .i64 a :: rest => some (decide (b.toInt ≤ a.toInt), rest)
  | .ult, .i32 b :: .i32 a :: rest => some (decide (a < b), rest)
  | .ult, .i64 b :: .i64 a :: rest => some (decide (a < b), rest)
  | .ne, .i32 b :: .i32 a :: rest => some (decide (a ≠ b), rest)
  | .ne, .i64 b :: .i64 a :: rest => some (decide (a ≠ b), rest)
  | _, _ => none

theorem branch_pure (kind : BranchKind) (target pc : Nat) (stack : List CIL.Value)
    (profile : CIL.FeatureProfile) :
    CIL.step (branchOp kind target) false pc [] 0 stack (fun _ => none) profile =
      (branchTest kind stack).map (fun (selected, values) =>
        CIL.Action.next (if selected then target else pc + 1) values (fun _ => none)) := by
  cases kind with
  | nonzero =>
    cases stack with
    | nil => rfl
    | cons value rest =>
      dsimp only [branchOp]
      delta CIL.step
      dsimp only [branchTest]
      cases CIL.truth value <;> rfl
  | ge | ult | ne =>
    cases stack with
    | nil => rfl
    | cons right tail =>
      cases tail with
      | nil => cases right <;> rfl
      | cons left rest =>
        cases right <;> first
          | rfl
          | (cases left <;> first
              | rfl
              | (dsimp only [branchOp]; delta CIL.step
                 dsimp only [branchTest, Option.map]; simp only [decide_eq_true_eq]; rfl))

theorem branch_form (body : CIL.Method) (kind : BranchKind) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) (target pc : Nat) : step body (branchOp kind target) pc args frame stack memory =
    (if stack.length < branchArity kind then .error .invalidState else do
      let values ← scalars (stack.take (branchArity kind))
      let some (selected, result) := branchTest kind values | .error .invalidState
      let checked ← (result.map Value.scalar).mapM (checkedValue memory)
      return .next (if selected then target else pc + 1) (checked ++ stack.drop (branchArity kind)) frame memory) := by
  have raw := branch_pure kind target pc
  cases kind <;> dsimp only [branchOp] <;> delta step <;> dsimp only [pureArity, branchArity]
  all_goals simp only [branchOp] at raw
  all_goals split <;> simp_all only [ite_true, ite_false]
  all_goals first
    | rfl
    | (congr 1; funext values; cases found : branchTest _ values with | none => rfl | some result => cases result <;> rfl)

theorem branch_relocate (body : CIL.Method) (kind : BranchKind) (target : Nat)
    (f : Nat → Nat) (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (successor : f (pc + 1) = f pc + 1) :
    step body (branchOp kind (f target)) (f pc) args frame stack memory =
      (step body (branchOp kind target) pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  have form := branch_form body kind args frame stack memory
  rw [form, form]
  split
  · rfl
  · simp only [Bind.bind, map_bind]
    congr 1
    funext values
    cases found : branchTest kind values with
    | none => rfl
    | some result =>
      rcases result with ⟨selected, result⟩
      simp only [map_bind, Pure.pure, Except.pure]
      congr 1
      funext checked
      cases selected <;> simp [Except.map, relocateAction, successor]

def convStack : List CIL.Value → Option (List CIL.Value)
  | value :: rest => (CIL.unary .convI8 value).map (· :: rest)
  | _ => none

theorem conv_pure (pc : Nat) (stack : List CIL.Value) (profile : CIL.FeatureProfile) :
    CIL.step .convI8 false pc [] 0 stack (fun _ => none) profile =
      (convStack stack).map (fun values => CIL.Action.next (pc + 1) values (fun _ => none)) := by
  cases stack with
  | nil => rfl
  | cons value rest =>
    delta CIL.step
    dsimp only [convStack]
    cases CIL.unary .convI8 value <;> rfl

theorem conv_form (body : CIL.Method) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) (pc : Nat) :
    step body .convI8 pc args frame stack memory =
    (if stack.length < 1 then .error .invalidState else do
      let values ← scalars (stack.take 1)
      let some result := convStack values | .error .invalidState
      let checked ← (result.map Value.scalar).mapM (checkedValue memory)
      return .next (pc + 1) (checked ++ stack.drop 1) frame memory) := by
  delta step
  dsimp only [pureArity]
  split
  · rfl
  · congr 1; funext values; rw [conv_pure]; cases convStack values <;> rfl

theorem conv_relocate (body : CIL.Method) (f : Nat → Nat) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) (successor : f (pc + 1) = f pc + 1) :
    step body .convI8 (f pc) args frame stack memory =
      (step body .convI8 pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  rw [conv_form, conv_form]
  split
  · rfl
  · simp only [Bind.bind, map_bind]
    congr 1
    funext values
    cases found : convStack values with
    | none => rfl
    | some result =>
      simp only [map_bind, Pure.pure, Except.pure]
      congr 1
      funext checked
      simp [Except.map, relocateAction, successor]
inductive Supported : CIL.Op → Prop where
  | arg (index : Nat) : Supported (.arg index)
  | conv : Supported .convI8
  | localValue (index : Nat) : Supported (.local index)
  | setLocal (index : Nat) : Supported (.setLocal index)
  | memory (op) : MemoryOp op → Supported op
  | binary (op) : BinaryOp op → Supported op
  | branch (kind target) : Supported (branchOp kind target)
  | call (callee argc : Nat) : Supported (.call callee argc)
  | ret : Supported .ret

def FlowResult (lower : Nat) (calleeAllowed : Nat → Prop) : FrameAction → Prop
  | .next pc _ _ _ => lower ≤ pc
  | .call callee _ _ _ => calleeAllowed callee
  | .returned _ _ => True
  | .construct .. => False

def FlowInput (lower : Nat) (calleeAllowed : Nat → Prop) : CIL.Op → Prop
  | .bge target | .bltu target | .bne target | .brnonzero target => lower ≤ target
  | .call callee _ => calleeAllowed callee
  | _ => True

theorem supported_flow (body : CIL.Method) (op : CIL.Op) (supported : Supported op)
    (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) (action : FrameAction)
    (lower : Nat) (calleeAllowed : Nat → Prop) (successor : lower ≤ pc + 1)
    (targets : FlowInput lower calleeAllowed op)
    (executed : step body op pc args frame stack memory = .ok action) : FlowResult lower calleeAllowed action := by
  cases supported
  case' conv => rw [conv_form] at executed
  case' memory allowed => rw [memory_form body op allowed] at executed
  case' binary allowed => rw [binary_form body op allowed] at executed
  case' branch kind target =>
    rw [branch_form body kind] at executed
    have targetBound : lower ≤ target := by cases kind <;> exact targets
    clear targets
  case' arg index => delta step at executed; dsimp only at executed
  case' localValue index => delta step at executed; dsimp only at executed
  case' setLocal index => cases stack <;> delta step at executed <;> dsimp only [pureArity] at executed
  case' call callee argc => delta step at executed; dsimp only at executed
  case' ret => delta step at executed; dsimp only at executed
  all_goals simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  iterate 14
    all_goals first
      | (solve | simp_all [FlowResult, FlowInput])
      | (split at executed <;> try simp_all)
      | (cases action <;> simp_all [FlowResult, FlowInput])
      | skip

def relocateOp (f : Nat → Nat) : CIL.Op → CIL.Op
  | .bge target => .bge (f target)
  | .bltu target => .bltu (f target)
  | .bne target => .bne (f target)
  | .brnonzero target => .brnonzero (f target)
  | op => op

theorem supported_relocate (body : CIL.Method) (op : CIL.Op) (supported : Supported op)
    (f : Nat → Nat) (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (successor : f (pc + 1) = f pc + 1) :
    step body (relocateOp f op) (f pc) args frame stack memory =
      (step body op pc args frame stack memory).map (relocateAction (fun _ => f) 0) := by
  cases supported with
  | arg index => exact arg_relocate body index f pc args frame stack memory successor
  | conv => exact conv_relocate body f pc args frame stack memory successor
  | localValue index => exact local_relocate body index f pc args frame stack memory successor
  | setLocal index => exact setLocal_relocate body index f pc args frame stack memory successor
  | memory op allowed =>
    have unchanged : relocateOp f op = op := by cases allowed <;> rfl
    rw [unchanged]
    exact memory_relocate body op allowed f pc args frame stack memory successor
  | binary op allowed =>
    have unchanged : relocateOp f op = op := by cases allowed <;> rfl
    rw [unchanged]
    exact binary_relocate body op allowed f pc args frame stack memory successor
  | branch kind target =>
    have changed : relocateOp f (branchOp kind target) = branchOp kind (f target) := by cases kind <;> rfl
    rw [changed]
    exact branch_relocate body kind target f pc args frame stack memory successor
  | call callee argc => exact call_relocate body callee argc f pc args frame stack memory
  | ret => exact return_relocate body f pc args frame stack memory

inductive StorageExtra : CIL.Op → Prop where
  | skipInit : StorageExtra .skipInit
  | dup : StorageExtra .dup
  | store64 : StorageExtra .store64
  | unsupported (message : String) : StorageExtra (.unsupported message)
  | memory (operation : CIL.MemoryOp) : StorageExtra (.memory operation)
  | feature (flag : CIL.Feature) : StorageExtra (.feature flag)
  | brzero (target : Nat) : StorageExtra (.brzero target)
  | intrinsic (operation : CIL.Intrinsic) (argc : Nat) : StorageExtra (.intrinsic operation argc)

theorem storage_extra_flow (body : CIL.Method) (op : CIL.Op) (supported : StorageExtra op)
    (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) (action : FrameAction)
    (executed : step body op pc args frame stack memory = .ok action) :
    FlowResult 0 (fun _ => False) action := by
  cases supported <;> delta step at executed <;> dsimp only [pureArity] at executed <;>
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at executed
  iterate 14
    all_goals first
      | (solve | simp_all [FlowResult])
      | (split at executed <;> try simp_all)
      | (cases action <;> simp_all [FlowResult])
      | skip


#print axioms supported_flow
#print axioms supported_relocate
#print axioms storage_extra_flow
end UInt256Proof.Transport
