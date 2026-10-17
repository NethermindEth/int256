import CIL.Safety.Execution
import CIL.Safety.StepComposition
import CIL.Safety.CallComposition
import CIL.Safety.FuelLemmas
import UInt256.Safety.Contract
import UInt256.Safety.ReportingContract

namespace UInt256Model.Safety.CodeExpansion
open CIL.Safety

/-- Moves branch targets by `f`, callee indices by `μ` and argument indices by `σ`. -/
def relabel (f μ σ : Nat → Nat) : CIL.Op → CIL.Op
  | .bgt t => .bgt (f t)
  | .ble t => .ble (f t)
  | .bleu t => .bleu (f t)
  | .branch t => .branch (f t)
  | .switch ts => .switch (ts.map f)
  | .brzero t => .brzero (f t)
  | .brnonzero t => .brnonzero (f t)
  | .bltu t => .bltu (f t)
  | .bgeu t => .bgeu (f t)
  | .bgtu t => .bgtu (f t)
  | .bge t => .bge (f t)
  | .blt t => .blt (f t)
  | .beq t => .beq (f t)
  | .bne t => .bne (f t)
  | .call c n => .call (μ c) n
  | .newVector256 c n => .newVector256 (μ c) n
  | .newAggregate c n s => .newAggregate (μ c) n s
  | .arg i k => .arg (σ i) k
  | op => op

/-- The frame action of a relabelled instruction. -/
def FrameAction.relabel (f μ : Nat → Nat) : FrameAction → FrameAction
  | .next t s fr m => .next (f t) s fr m
  | .call c a r m => .call (μ c) a r m
  | .construct c a r fr t k m => .construct (μ c) a r fr t k m
  | .returned v m => .returned v m

/-- Instructions whose step depends only on the stack, frame, memory and profile. -/
def supported : CIL.Op → Bool
  | .add | .band | .bor | .bgeu _ | .branch _ | .brnonzero _ | .brzero _ | .convI8 | .eq | .gtu | .feature _
  | .const32 _ | .dup | .pop | .fieldAddress _ | .fieldAt _ _ _ | .store64 | .skipInit | .unsupported _
  | .arg _ _ | .local _ _ | .setLocal _ _ | .call _ _ | .intrinsic _ _ | .memory _ | .ret _ => true
  | _ => false

def actionRelabel (f : Nat → Nat) : CIL.Action → CIL.Action
  | .next t s m => .next (f t) s m
  | a => a

macro "cil_case" : tactic => `(tactic| (
  unfold CIL.step
  (repeat' split) <;> simp_all [actionRelabel, Bind.bind, Option.bind, Pure.pure]
  all_goals first
    | (cases CIL.binary _ _ _ <;> simp_all [actionRelabel])
    | (cases CIL.unary _ _ <;> simp_all [actionRelabel])))



theorem cil_add (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step .add false pc' [] 0 vs (fun _ => none) p =
      (CIL.step .add false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  cil_case

theorem cil_band (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step .band false pc' [] 0 vs (fun _ => none) p =
      (CIL.step .band false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  cil_case

theorem cil_bor (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step .bor false pc' [] 0 vs (fun _ => none) p =
      (CIL.step .bor false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  cil_case

theorem cil_convI8 (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step .convI8 false pc' [] 0 vs (fun _ => none) p =
      (CIL.step .convI8 false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  cil_case

theorem cil_eq (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step .eq false pc' [] 0 vs (fun _ => none) p =
      (CIL.step .eq false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  cil_case

theorem cil_gtu (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step .gtu false pc' [] 0 vs (fun _ => none) p =
      (CIL.step .gtu false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  cil_case

theorem cil_feature (x : CIL.Feature) (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step (.feature x) false pc' [] 0 vs (fun _ => none) p =
      (CIL.step (.feature x) false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  cil_case

theorem cil_branch (t : Nat) (pc pc' : Nat) (f : Nat → Nat) (_next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step (.branch (f t)) false pc' [] 0 vs (fun _ => none) p =
      (CIL.step (.branch t) false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  rcases vs with _ | ⟨v, _ | ⟨w, rest⟩⟩ <;> simp only [CIL.step] <;> (try cases CIL.truth v) <;>
    simp [actionRelabel, Pure.pure] <;> (try split) <;> simp_all

theorem cil_brzero (t : Nat) (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step (.brzero (f t)) false pc' [] 0 vs (fun _ => none) p =
      (CIL.step (.brzero t) false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  rcases vs with _ | ⟨v, _ | ⟨w, rest⟩⟩ <;> simp only [CIL.step] <;> (try cases CIL.truth v) <;>
    simp [actionRelabel, Bind.bind, Option.bind, Pure.pure] <;> (try split) <;> simp_all

theorem cil_brnonzero (t : Nat) (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step (.brnonzero (f t)) false pc' [] 0 vs (fun _ => none) p =
      (CIL.step (.brnonzero t) false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  rcases vs with _ | ⟨v, _ | ⟨w, rest⟩⟩ <;> simp only [CIL.step] <;> (try cases CIL.truth v) <;>
    simp [actionRelabel, Bind.bind, Option.bind, Pure.pure] <;> (try split) <;> simp_all

theorem cil_bgeu (t : Nat) (pc pc' : Nat) (f : Nat → Nat) (next : f (pc + 1) = pc' + 1) (vs : List CIL.Value)
    (p : CIL.FeatureProfile) :
    CIL.step (.bgeu (f t)) false pc' [] 0 vs (fun _ => none) p =
      (CIL.step (.bgeu t) false pc [] 0 vs (fun _ => none) p).map (actionRelabel f) := by
  rcases vs with _ | ⟨v, _ | ⟨w, rest⟩⟩ <;> simp only [CIL.step]
  all_goals (try rfl)
  all_goals cases v <;> cases w <;>
    simp [actionRelabel, Pure.pure] <;> (try split) <;> simp_all

theorem static_nil (b b' : CIL.Method) (static : b.staticSites = []) (static' : b'.staticSites = [])
    (pc pc' : Nat) (operation : CIL.MemoryOp) (stack : List Value) (m : Memory) :
    staticInstruction b' pc' operation stack m = staticInstruction b pc operation stack m := by
  unfold staticInstruction
  simp [static, static']

/-- A supported instruction steps identically after relabelling, up to its targets. -/
theorem step_relabel (b b' : CIL.Method) (profile : b'.profile = b.profile)
    (returns : b'.returnsValue = b.returnsValue) (static : b.staticSites = []) (static' : b'.staticSites = [])
    (op : CIL.Op) (plain : supported op = true) (pc pc' : Nat) (f μ σ : Nat → Nat) (next : f (pc + 1) = pc' + 1)
    (args args' : List Value) (moved : ∀ i, args'[σ i]? = args[i]?) (frame : Frame) (stack : List Value)
    (m : Memory) (a : FrameAction) (h : step b op pc args frame stack m = .ok a) :
    step b' (relabel f μ σ op) pc' args' frame stack m = .ok (FrameAction.relabel f μ a) := by
  cases op <;> try cases ‹Option CIL.NarrowKind›
  all_goals simp only [supported, Bool.false_eq_true] at plain
  all_goals simp only [relabel]
  all_goals unfold step at h ⊢
  all_goals simp only [profile, returns, pureArity, static_nil b b' static static' pc pc',
      Bind.bind, Except.bind, Pure.pure, Except.pure, moved] at h ⊢
  all_goals
    rcases stack with _ | ⟨v, rest⟩ <;> (try simp only at h ⊢) <;> (repeat' split at h) <;> (try simp only [Except.ok.injEq] at h) <;> (try subst_vars) <;>
      simp_all [FrameAction.relabel, cil_add pc pc' f next, cil_band pc pc' f next, cil_bor pc pc' f next,
        cil_convI8 pc pc' f next, cil_eq pc pc' f next, cil_gtu pc pc' f next, cil_feature _ pc pc' f next,
        cil_branch _ pc pc' f next, cil_brzero _ pc pc' f next, cil_brnonzero _ pc pc' f next, cil_bgeu _ pc pc' f next,
        actionRelabel]

/-- How one source instruction is rewritten in the expanded body. -/
inductive Edit where
  | keep
  | dup
  | call (helper : Nat)
  | fold (helper : Nat)
  | reverse (locals : List Nat) (callee argc : Nat)
  | skip
  deriving DecidableEq

def Edit.size : Edit → Nat
  | .keep => 1
  | .dup => 3
  | .call _ => 1
  | .fold _ => 1
  | .reverse locals _ _ => locals.length + 1
  | .skip => 0

def editAt (edits : List (Nat × Edit)) (pc : Nat) : Edit :=
  match edits.find? (fun e => e.1 == pc) with
  | some e => e.2
  | none => .keep

/-- The expanded program counter of a source program counter. -/
def position (edits : List (Nat × Edit)) : Nat → Nat
  | 0 => 0
  | n + 1 => position edits n + (editAt edits n).size

def chunk (edits : List (Nat × Edit)) (μ σ : Nat → Nat) (pc : Nat) (op : CIL.Op) : List CIL.Op :=
  match editAt edits pc with
  | .keep => [relabel (position edits) μ σ op]
  | .dup => [op, op, .band]
  | .call h => [.call h 2]
  | .fold h => [.call h 2]
  | .reverse locals callee argc => locals.reverse.map (fun l => .local l none) ++ [.call (μ callee) argc]
  | .skip => []

def expandFrom (edits : List (Nat × Edit)) (μ σ : Nat → Nat) : Nat → List CIL.Op → List CIL.Op
  | _, [] => []
  | pc, op :: rest => chunk edits μ σ pc op ++ expandFrom edits μ σ (pc + 1) rest

/-- Rewrites a body instruction by instruction according to its edits. -/
def expand (edits : List (Nat × Edit)) (μ σ : Nat → Nat) (code : List CIL.Op) : List CIL.Op :=
  expandFrom edits μ σ 0 code

theorem chunk_length (edits : List (Nat × Edit)) (μ σ : Nat → Nat) (pc : Nat) (op : CIL.Op) :
    (chunk edits μ σ pc op).length = (editAt edits pc).size := by
  unfold chunk
  split <;> simp_all [Edit.size]

theorem position_mono (edits : List (Nat × Edit)) (s n : Nat) : position edits s ≤ position edits (s + n) := by
  induction n with
  | zero => simp
  | succ n ih => exact Nat.le_trans ih (by simp [position])

theorem expandFrom_fetch (edits : List (Nat × Edit)) (μ σ : Nat → Nat) (op : CIL.Op) (k : Nat) :
    ∀ (code : List CIL.Op) (s pc : Nat), code[pc]? = some op → k < (editAt edits (s + pc)).size →
      (expandFrom edits μ σ s code)[position edits (s + pc) - position edits s + k]? =
        (chunk edits μ σ (s + pc) op)[k]? := by
  intro code
  induction code with
  | nil => intro s pc found; simp at found
  | cons head rest ih =>
    intro s pc found small
    cases pc with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp only [Nat.add_zero, Nat.sub_self, Nat.zero_add, expandFrom]
      rw [List.getElem?_append_left (by rw [chunk_length]; simpa using small)]
    | succ pc =>
      simp only [List.getElem?_cons_succ] at found
      have step := ih (s + 1) pc found (by simpa [Nat.add_assoc, Nat.add_comm 1 pc] using small)
      have mono := position_mono edits (s + 1) pc
      have first : position edits (s + 1) = position edits s + (editAt edits s).size := rfl
      simp only [expandFrom]
      rw [List.getElem?_append_right (by rw [chunk_length]; rw [show s + (pc + 1) = s + 1 + pc by omega]; omega),
        chunk_length]
      rw [show s + (pc + 1) = s + 1 + pc by omega]
      rw [show position edits (s + 1 + pc) - position edits s + k - (editAt edits s).size =
        position edits (s + 1 + pc) - position edits (s + 1) + k by omega]
      exact step

theorem expand_fetch (edits : List (Nat × Edit)) (μ σ : Nat → Nat) (code : List CIL.Op) (pc : Nat) (op : CIL.Op)
    (found : code[pc]? = some op) (k : Nat) (small : k < (editAt edits pc).size) :
    (expand edits μ σ code)[position edits pc + k]? = (chunk edits μ σ pc op)[k]? := by
  have := expandFrom_fetch edits μ σ op k code 0 pc found (by simpa using small)
  simpa [expand, position] using this

/-- A private helper applying a binary intrinsic to its two arguments. -/
def callHelper (profile : CIL.FeatureProfile) (operation : CIL.Intrinsic) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .arg 1, .intrinsic operation 2, .ret] }

/-- A private helper applying a ternary intrinsic with a fixed constant operand. -/
def foldHelper (profile : CIL.FeatureProfile) (word : BitVec 32) (operation : CIL.Intrinsic) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .arg 1, .const32 word, .intrinsic operation 3, .ret] }

theorem checked_scalar (m : Memory) (value : CIL.Value) (numeric : numericValue value = true) :
    checkedValue m (.scalar value) = .ok (.scalar value) := by
  simp [checkedValue, numeric]

theorem scalars_two {a b : Value} {operands : List CIL.Value} (h : scalars [b, a] = .ok operands) :
    ∃ x y, b = .scalar x ∧ a = .scalar y ∧ numericValue x = true ∧ numericValue y = true ∧ operands = [x, y] := by
  rcases b with x | _ | _ <;> rcases a with y | _ | _ <;> simp [scalars] at h <;>
    cases hx : numericValue x <;> (try cases hy : numericValue y) <;> simp_all [Functor.map, Except.map]
  all_goals exact h.symm

theorem intrinsic_two_step (b : CIL.Method) (i : CIL.Intrinsic) (pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (m : Memory) (act : FrameAction) (h : step b (.intrinsic i 2) pc args frame stack m = .ok act) :
    ∃ x y rest value, stack = .scalar y :: .scalar x :: rest ∧ numericValue x = true ∧ numericValue y = true ∧
      i.available b.profile = true ∧ checkedIntrinsic i [x, y] = .ok value ∧ numericValue value = true ∧
      act = .next (pc + 1) (.scalar value :: rest) frame m := by
  rcases stack with _ | ⟨a, _ | ⟨c, rest⟩⟩ <;>
    simp [step, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · split at h <;> simp at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    rename_i available
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i operands scalarsOk
    split at h
    · simp at h
    rename_i value intrinsicOk
    split at h
    · simp at h
    rename_i checked checkedOk
    obtain ⟨x, y, rfl, rfl, nx, ny, rfl⟩ := scalars_two scalarsOk
    cases numeric : numericValue value <;> simp [checkedValue, numeric] at checkedOk
    subst checkedOk
    simp only [Except.ok.injEq] at h
    exact ⟨x, y, rest, value, rfl, nx, ny, by simpa using available, intrinsicOk, numeric, h.symm⟩

theorem call_helper_invoke {Q : CIL.Program} {h : Nat} {profile : CIL.FeatureProfile} {i : CIL.Intrinsic}
    {x y value : CIL.Value} (m : Memory) (helper : Q[h]? = some (callHelper profile i))
    (available : i.available profile = true) (nx : numericValue x = true) (ny : numericValue y = true)
    (intrinsic : checkedIntrinsic i [x, y] = .ok value) (nv : numericValue value = true) :
    invoke Q 5 h [.scalar x, .scalar y] m = .ok (m, [.scalar value]) := by
  simp [invoke, helper, callHelper, checkedValue, nx, ny, enterFrame, makeLocals, makeArgumentHomes,
    makeParameterHomes, run, step, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError,
    scalars, available, intrinsic, nv, leaveFrame]

def isFeature : CIL.Op → Bool
  | .feature _ => true
  | _ => false

def targets : CIL.Op → List Nat
  | .bgt t | .ble t | .bleu t | .branch t | .brzero t | .brnonzero t | .bltu t | .bgeu t | .bgtu t | .bge t
  | .blt t | .beq t | .bne t => [t]
  | .switch ts => ts
  | _ => []

/-- The argument index in the expanded callee of each source argument index. -/
def argMap (table : List Nat) (i : Nat) : Nat := table.getD i i

/-- Reverses the last `count` of `argc` arguments. -/
def reversal (argc count : Nat) : List Nat :=
  List.range (argc - count) ++ (List.range count).reverse.map (· + (argc - count))

def directCall (perm : Nat → List Nat) : CIL.Op → Bool
  | .call c _ => perm c == []
  | _ => true

def isPush (l : Nat) : CIL.Op → Bool
  | .local l' none => l' == l
  | _ => false

def isCall (callee argc : Nat) : CIL.Op → Bool
  | .call c n => c == callee && n == argc
  | _ => false

/-- The source code holds the pushes of `locals` from `pc` on. -/
def pushesAt (code : List CIL.Op) : Nat → List Nat → Bool
  | _, [] => true
  | pc, l :: rest => (code[pc]?).any (isPush l) && pushesAt code (pc + 1) rest

/-- The `count` source instructions after `pc` are absorbed into the edit at `pc`. -/
def skipsAfter (edits : List (Nat × Edit)) (pc : Nat) : Nat → Bool
  | 0 => true
  | count + 1 => editAt edits (pc + count + 1) == .skip && skipsAfter edits pc count

def editOk (edits : List (Nat × Edit)) (perm : Nat → List Nat) (code : List CIL.Op) (pc : Nat) (op : CIL.Op) :
    Bool :=
  match editAt edits pc with
  | .keep => supported op && directCall perm op && (targets op).all (fun t => editAt edits t != .skip) &&
      editAt edits (pc + 1) != .skip
  | .dup => isFeature op && editAt edits (pc + 1) != .skip
  | .call _ => editAt edits (pc + 1) != .skip
  | .fold _ => editAt edits (pc + 1) == .skip && editAt edits (pc + 2) != .skip
  | .reverse locals callee argc => pushesAt code pc locals &&
      (code[pc + locals.length]?).any (isCall callee argc) && skipsAfter edits pc locals.length &&
      editAt edits (pc + locals.length + 1) != .skip && decide (locals.length ≤ argc) &&
      perm callee == reversal argc locals.length
  | .skip => true

/-- Edits keep control flow inside the expanded instructions and fold only constant-operand pairs. -/
def checkCode (edits : List (Nat × Edit)) (perm : Nat → List Nat) (code : List CIL.Op) : Bool :=
  editAt edits 0 != .skip &&
    (List.range code.length).all fun pc => match code[pc]? with
      | some op => editOk edits perm code pc op
      | none => true

theorem checkCode_entry {edits : List (Nat × Edit)} {perm : Nat → List Nat} {code : List CIL.Op}
    (h : checkCode edits perm code = true) :
    editAt edits 0 ≠ .skip := by
  simp only [checkCode, Bool.and_eq_true, bne_iff_ne] at h
  exact h.1

theorem checkCode_at {edits : List (Nat × Edit)} {perm : Nat → List Nat} {code : List CIL.Op}
    (h : checkCode edits perm code = true) {pc : Nat} {op : CIL.Op} (found : code[pc]? = some op) :
    editOk edits perm code pc op = true := by
  simp only [checkCode, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have bound : pc < code.length := by
    rcases Nat.lt_or_ge pc code.length with lt | ge
    · exact lt
    · simp [List.getElem?_eq_none ge] at found
  simpa [found] using h.2 pc bound

theorem relabel_fix (f : Nat → Nat) (op : CIL.Op) (fixed : ∀ t ∈ targets op, f t = t) :
    relabel f id id op = op := by
  cases op <;> simp_all [relabel, targets]
  case switch ts => exact List.map_congr_left fixed |>.trans (List.map_id ts)

theorem step_target (b : CIL.Method) (static : b.staticSites = []) (op : CIL.Op) (plain : supported op = true)
    (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (t : Nat) (s : List Value) (fr : Frame) (m' : Memory)
    (h : step b op pc args frame stack m = .ok (.next t s fr m')) : t = pc + 1 ∨ t ∈ targets op := by
  classical
  let f : Nat → Nat := fun x => if x = pc + 1 ∨ x ∈ targets op then x else pc + 1
  have moved := step_relabel b b rfl rfl static static op plain pc pc f id id (by simp [f]) args args (fun _ => rfl)
    frame stack m _ h
  rw [relabel_fix f op (fun x member => by simp [f, member])] at moved
  rw [h] at moved
  simp only [FrameAction.relabel, Except.ok.injEq, FrameAction.next.injEq] at moved
  by_cases c : t = pc + 1 ∨ t ∈ targets op
  · exact c
  · simp only [f, c, ite_false] at moved
    exact Or.inl moved.1

theorem feature_step (b : CIL.Method) (x : CIL.Feature) (pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (m : Memory) :
    step b (.feature x) pc args frame stack m =
      .ok (.next (pc + 1) (.scalar (.i32 (if b.profile.evaluate x then 1 else 0)) :: stack) frame m) := by
  simp [step, pureArity, scalars, CIL.step, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

theorem band_same_step (b : CIL.Method) (v : BitVec 32) (pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (m : Memory) :
    step b .band pc args frame (.scalar (.i32 v) :: .scalar (.i32 v) :: stack) m =
      .ok (.next (pc + 1) (.scalar (.i32 v) :: stack) frame m) := by
  simp [step, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

theorem const_step (b : CIL.Method) (c : BitVec 32) (pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (m : Memory) :
    step b (.const32 c) pc args frame stack m = .ok (.next (pc + 1) (.scalar (.i32 c) :: stack) frame m) := by
  simp [step, pureArity, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem scalars_three {a b : Value} {c : BitVec 32} {operands : List CIL.Value}
    (h : scalars [b, a, .scalar (.i32 c)] = .ok operands) :
    ∃ x y, b = .scalar x ∧ a = .scalar y ∧ numericValue x = true ∧ numericValue y = true ∧
      operands = [x, y, .i32 c] := by
  rcases b with x | _ | _ <;> rcases a with y | _ | _ <;> simp [scalars] at h <;>
    cases hx : numericValue x <;> (try cases hy : numericValue y) <;>
    simp_all [Functor.map, Except.map, numericValue]
  all_goals exact h.symm

theorem intrinsic_three_step (b : CIL.Method) (i : CIL.Intrinsic) (c : BitVec 32) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (act : FrameAction)
    (h : step b (.intrinsic i 3) pc args frame (.scalar (.i32 c) :: stack) m = .ok act) :
    ∃ x y rest value, stack = .scalar y :: .scalar x :: rest ∧ numericValue x = true ∧ numericValue y = true ∧
      i.available b.profile = true ∧ checkedIntrinsic i [x, y, .i32 c] = .ok value ∧ numericValue value = true ∧
      act = .next (pc + 1) (.scalar value :: rest) frame m := by
  rcases stack with _ | ⟨a, _ | ⟨d, rest⟩⟩ <;>
    simp [step, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · split at h <;> simp at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    rename_i available
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i operands scalarsOk
    split at h
    · simp at h
    rename_i value intrinsicOk
    split at h
    · simp at h
    rename_i checked checkedOk
    obtain ⟨x, y, rfl, rfl, nx, ny, rfl⟩ := scalars_three scalarsOk
    cases numeric : numericValue value <;> simp [checkedValue, numeric] at checkedOk
    subst checkedOk
    simp only [Except.ok.injEq] at h
    exact ⟨x, y, rest, value, rfl, nx, ny, by simpa using available, intrinsicOk, numeric, h.symm⟩

theorem fold_helper_invoke {Q : CIL.Program} {h : Nat} {profile : CIL.FeatureProfile} {c : BitVec 32}
    {i : CIL.Intrinsic} {x y value : CIL.Value} (m : Memory) (helper : Q[h]? = some (foldHelper profile c i))
    (available : i.available profile = true) (nx : numericValue x = true) (ny : numericValue y = true)
    (intrinsic : checkedIntrinsic i [x, y, .i32 c] = .ok value) (nv : numericValue value = true) :
    invoke Q 6 h [.scalar x, .scalar y] m = .ok (m, [.scalar value]) := by
  have enter : enterFrame (foldHelper profile c i) [.scalar x, .scalar y] m = .ok (⟨m.nextIdentity, [], [], []⟩, m) := by
    simp [enterFrame, foldHelper, makeLocals, makeArgumentHomes, makeParameterHomes, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  simp only [invoke, helper, List.mapM_cons, List.mapM_nil, checkedValue, nx, ny, ite_true, enter,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError]
  rw [run_next (pc := 0) helper rfl (by simp [step, checkedValue, nx, Bind.bind, Except.bind, Pure.pure, Except.pure]; exact ⟨rfl, rfl, rfl, rfl⟩)]
  rw [run_next (pc := 1) helper rfl (by simp [step, checkedValue, ny, Bind.bind, Except.bind, Pure.pure, Except.pure]; exact ⟨rfl, rfl, rfl, rfl⟩)]
  rw [run_next (pc := 2) helper rfl (const_step _ c 2 _ _ _ m)]
  have s3 : step (foldHelper profile c i) (.intrinsic i 3) 3 [.scalar x, .scalar y] ⟨m.nextIdentity, [], [], []⟩
      [.scalar (.i32 c), .scalar y, .scalar x] m =
      .ok (.next 4 [.scalar value] ⟨m.nextIdentity, [], [], []⟩ m) := by
    simp [step, foldHelper, available, scalars, nx, ny, show numericValue (.i32 c) = true from rfl, intrinsic,
      checkedValue, nv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [run_next (pc := 3) helper rfl s3]
  simp [run, helper, foldHelper, step, checkedValue, nv, leaveFrame, Bind.bind, Except.bind, Pure.pure,
    Except.pure, Except.mapError]

theorem call_two_step (b : CIL.Method) (h : Nat) (pc : Nat) (args : List Value) (frame : Frame)
    (x y : CIL.Value) (rest : List Value) (m : Memory) (nx : numericValue x = true) (ny : numericValue y = true) :
    step b (.call h 2) pc args frame (.scalar y :: .scalar x :: rest) m =
      .ok (.call h [.scalar x, .scalar y] rest m) := by
  simp [step, checkedValue, nx, ny, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `Q` is `P` with every body expanded by its edits and the referenced helpers present. -/
structure Expansion (P Q : CIL.Program) (μ : Nat → Nat) (E : Nat → List (Nat × Edit)) (perm : Nat → List Nat) :
    Prop where
  body : ∀ (m : Nat) (b : CIL.Method), P[m]? = some b →
    Q[μ m]? = some { b with code := expand (E m) μ (argMap (perm m)) b.code }
  static : ∀ (m : Nat) (b : CIL.Method), P[m]? = some b → b.staticSites = []
  frames : ∀ (m : Nat) (b : CIL.Method), P[m]? = some b → b.vectorArgs = [] ∧ b.parameterHomes = []
  checked : ∀ (m : Nat) (b : CIL.Method), P[m]? = some b → checkCode (E m) perm b.code = true
  calls : ∀ (m : Nat) (b : CIL.Method), P[m]? = some b → ∀ pc h, (pc, Edit.call h) ∈ E m →
    ∃ i, b.code[pc]? = some (.intrinsic i 2) ∧ Q[h]? = some (callHelper b.profile i)
  folds : ∀ (m : Nat) (b : CIL.Method), P[m]? = some b → ∀ pc h, (pc, Edit.fold h) ∈ E m →
    ∃ c i, b.code[pc]? = some (.const32 c) ∧ b.code[pc + 1]? = some (.intrinsic i 3) ∧
      Q[h]? = some (foldHelper b.profile c i)

theorem editAt_mem {edits : List (Nat × Edit)} {pc : Nat} {e : Edit} (h : editAt edits pc = e) (ne : e ≠ .keep) :
    (pc, e) ∈ edits := by
  unfold editAt at h
  split at h
  · rename_i found heq
    have member := List.mem_of_find?_eq_some heq
    have hit := List.find?_some heq
    simp only [beq_iff_eq] at hit
    subst h
    obtain ⟨first, second⟩ := found
    simp only at hit
    subst hit
    exact member
  · exact absurd h.symm ne

theorem enterFrame_code (b : CIL.Method) (code : List CIL.Op) (args : List Value) (m : Memory) :
    enterFrame { b with code := code } args m = enterFrame b args m := rfl

theorem no_construct (b : CIL.Method) (op : CIL.Op) (plain : supported op = true) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (c : Nat) (a rest : List Value) (fr : Frame) (t : Reference)
    (kind : CIL.LocalKind) (m' : Memory)
    (h : step b op pc args frame stack m = .ok (.construct c a rest fr t kind m')) : False := by
  cases op <;> simp only [supported, Bool.false_eq_true] at plain <;> unfold step at h <;>
    simp only [pureArity, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    rcases stack with _ | ⟨v, rest⟩ <;> (try simp only at h) <;> (repeat' split at h) <;> simp_all

theorem call_op (b : CIL.Method) (op : CIL.Op) (plain : supported op = true) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) (c : Nat) (a rest : List Value) (m' : Memory)
    (h : step b op pc args frame stack m = .ok (.call c a rest m')) : ∃ n, op = .call c n := by
  cases op <;> simp only [supported, Bool.false_eq_true] at plain <;> unfold step at h <;>
    simp only [pureArity, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  case call callee argc =>
    refine ⟨argc, ?_⟩
    split at h
    · simp at h
    · split at h <;> simp_all
  all_goals
    rcases stack with _ | ⟨v, rest⟩ <;> (try simp only at h) <;> (repeat' split at h) <;> simp_all

theorem argMap_nil : argMap [] = id := by
  funext i
  simp [argMap]

theorem isPush_eq {l : Nat} {o : Option CIL.Op} (h : o.any (isPush l) = true) : o = some (.local l none) := by
  rcases o with _ | op
  · simp at h
  · simp only [Option.any_some] at h
    cases op <;> (try cases ‹Option CIL.NarrowKind›) <;> simp_all [isPush]

theorem isCall_eq {c n : Nat} {o : Option CIL.Op} (h : o.any (isCall c n) = true) : o = some (.call c n) := by
  rcases o with _ | op
  · simp at h
  · simp only [Option.any_some] at h
    cases op <;> simp_all [isCall]

theorem local_push {b : CIL.Method} {l pc : Nat} {args : List Value} {frame : Frame} {stack : List Value}
    {m : Memory} {act : FrameAction} (h : step b (.local l none) pc args frame stack m = .ok act) :
    ∃ v, act = .next (pc + 1) (v :: stack) frame m ∧
      ∀ (b' : CIL.Method) (pc' : Nat) (args' stack' : List Value),
        step b' (.local l none) pc' args' frame stack' m = .ok (.next (pc' + 1) (v :: stack') frame m) := by
  unfold step at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hs : frame.locals[l]? with
  | none => simp [hs] at h
  | some slot =>
    cases hv : loadLocal m slot with
    | error e => simp [hs, hv] at h
    | ok v =>
      simp only [hs, hv, Except.ok.injEq] at h
      refine ⟨v, h.symm, fun b' pc' args' stack' => ?_⟩
      unfold step
      simp only [hs, hv, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Pure local pushes in the source leave their values on the stack in push order. -/
theorem pushes_source {P : CIL.Program} {m : Nat} {b : CIL.Method} (found : P[m]? = some b)
    (args : List Value) (frame : Frame) (mem : Memory) (r : Memory × List Value) :
    ∀ (locals : List Nat) (p k : Nat) (stack : List Value), pushesAt b.code p locals = true →
      run P k m p args frame stack mem = .ok r →
      ∃ pairs : List (Nat × Value), pairs.map Prod.fst = locals ∧ locals.length ≤ k ∧
        (∀ x ∈ pairs, ∀ (b' : CIL.Method) (pc' : Nat) (args' stack' : List Value),
          step b' (.local x.1 none) pc' args' frame stack' mem =
            .ok (.next (pc' + 1) (x.2 :: stack') frame mem)) ∧
        run P (k - locals.length) m (p + locals.length) args frame
          ((pairs.map Prod.snd).reverse ++ stack) mem = .ok r := by
  intro locals
  induction locals with
  | nil =>
    intro p k stack _ ran
    exact ⟨[], rfl, Nat.zero_le _, by simp, by simpa using ran⟩
  | cons l rest ih =>
    intro p k stack pushes ran
    simp only [pushesAt, Bool.and_eq_true] at pushes
    obtain ⟨here, later⟩ := pushes
    have fetch := isPush_eq here
    cases k with
    | zero => simp [run] at ran
    | succ k =>
    cases hs : step b (.local l none) p args frame stack mem with
    | error e => simp [run, found, fetch, hs, Except.mapError, Bind.bind, Except.bind] at ran
    | ok act =>
    obtain ⟨v, rfl, anyStep⟩ := local_push hs
    rw [run_next found fetch hs] at ran
    obtain ⟨pairs, names, enough, steps, ranRest⟩ := ih (p + 1) k (v :: stack) later ran
    refine ⟨(l, v) :: pairs, by simp [names], by simp; omega, ?_, ?_⟩
    · intro x member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact anyStep
      · exact steps x member
    · simp only [List.length_cons, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [show k + 1 - (rest.length + 1) = k - rest.length by omega,
        show p + (rest.length + 1) = p + 1 + rest.length by omega]
      exact ranRest

/-- The expanded pushes run straight through to the instruction after them. -/
theorem pushes_target {Q : CIL.Program} {mq : Nat} {b' : CIL.Method} (found : Q[mq]? = some b')
    (args : List Value) (frame : Frame) (mem : Memory) :
    ∀ (pairs : List (Nat × Value)) (q f : Nat) (stack : List Value),
      (∀ j, j < pairs.length → b'.code[q + j]? = (pairs.map fun x => CIL.Op.local x.1 none)[j]?) →
      (∀ x ∈ pairs, ∀ (pc' : Nat) (stack' : List Value),
        step b' (.local x.1 none) pc' args frame stack' mem = .ok (.next (pc' + 1) (x.2 :: stack') frame mem)) →
      run Q (f + pairs.length) mq q args frame stack mem =
        run Q f mq (q + pairs.length) args frame ((pairs.map Prod.snd).reverse ++ stack) mem := by
  intro pairs
  induction pairs with
  | nil => intro q f stack _ _; simp
  | cons x rest ih =>
    intro q f stack codes steps
    have c0 : b'.code[q]? = some (.local x.1 none) := by simpa using codes 0 (by simp)
    rw [show f + (x :: rest).length = f + rest.length + 1 by simp; omega]
    rw [run_next found c0 (steps x (by simp) q stack)]
    rw [ih (q + 1) f (x.2 :: stack)
      (fun j small => by
        have := codes (j + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
      (fun y member => steps y (by simp [member]))]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem call_step_ok {b : CIL.Method} {c n pc : Nat} {args : List Value} {frame : Frame} {stack : List Value}
    {m : Memory} {act : FrameAction} (h : step b (.call c n) pc args frame stack m = .ok act) :
    n ≤ stack.length ∧ ∃ a, (stack.take n).reverse.mapM (checkedValue m) = .ok a ∧
      act = .call c a (stack.drop n) m := by
  unfold step at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i long
    cases hm : (stack.take n).reverse.mapM (checkedValue m) with
    | error e => simp [hm] at h
    | ok a =>
      simp only [hm, Except.ok.injEq] at h
      exact ⟨by omega, a, rfl, h.symm⟩

theorem call_step_of {b : CIL.Method} {c n pc : Nat} {args : List Value} {frame : Frame} {stack : List Value}
    {m : Memory} {a : List Value} (long : n ≤ stack.length)
    (checked : (stack.take n).reverse.mapM (checkedValue m) = .ok a) :
    step b (.call c n) pc args frame stack m = .ok (.call c a (stack.drop n) m) := by
  unfold step
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, checked]
  split
  · omega
  · rfl

theorem mapM_length {f : Value → ExecutionResult Value} :
    ∀ {l r : List Value}, l.mapM f = .ok r → r.length = l.length := by
  intro l
  induction l with
  | nil => intro r h; simp [Pure.pure, Except.pure] at h; simp [← h]
  | cons x xs ih =>
    intro r h
    simp only [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hx : f x with
    | error e => simp [hx] at h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs] at h
      | ok ys =>
        simp only [hx, hxs, Except.ok.injEq] at h
        subst h
        simp [ih hxs]

theorem mapM_append_ok {f : Value → ExecutionResult Value} {l₁ l₂ r : List Value}
    (h : (l₁ ++ l₂).mapM f = .ok r) :
    ∃ r₁ r₂, l₁.mapM f = .ok r₁ ∧ l₂.mapM f = .ok r₂ ∧ r = r₁ ++ r₂ := by
  rw [List.mapM_append] at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases h₁ : l₁.mapM f with
  | error e => simp [h₁] at h
  | ok r₁ =>
    cases h₂ : l₂.mapM f with
    | error e => simp [h₁, h₂] at h
    | ok r₂ =>
      simp only [h₁, h₂, Except.ok.injEq] at h
      exact ⟨r₁, r₂, rfl, rfl, h.symm⟩

theorem mapM_append_of {f : Value → ExecutionResult Value} {l₁ l₂ r₁ r₂ : List Value}
    (h₁ : l₁.mapM f = .ok r₁) (h₂ : l₂.mapM f = .ok r₂) : (l₁ ++ l₂).mapM f = .ok (r₁ ++ r₂) := by
  rw [List.mapM_append]
  simp [h₁, h₂, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem mapM_reverse_ok {f : Value → ExecutionResult Value} :
    ∀ {l r : List Value}, l.mapM f = .ok r → l.reverse.mapM f = .ok r.reverse := by
  intro l
  induction l with
  | nil =>
    intro r h
    simp [Pure.pure, Except.pure] at h
    subst h
    rfl
  | cons x xs ih =>
    intro r h
    simp only [List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hx : f x with
    | error e => simp [hx] at h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => simp [hx, hxs] at h
      | ok ys =>
        simp only [hx, hxs, Except.ok.injEq] at h
        subst h
        rw [List.reverse_cons, List.reverse_cons]
        exact mapM_append_of (ih hxs) (by simp [hx, Bind.bind, Except.bind, Pure.pure, Except.pure])

theorem reversal_entry (argc count i : Nat) (fits : count ≤ argc) :
    (reversal argc count)[i]? = if i < argc - count then some i else if i < argc then
      some (argc - count + (count - 1 - (i - (argc - count)))) else none := by
  unfold reversal
  by_cases first : i < argc - count
  · rw [List.getElem?_append_left (by simpa using first)]
    simp [first]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_range, first, ite_false]
    by_cases second : i < argc
    · simp only [second, ite_true, List.getElem?_map]
      rw [List.getElem?_reverse (by simp; omega)]
      simp only [List.length_range]
      rw [List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      omega
    · simp only [second, ite_false]
      rw [List.getElem?_eq_none (by simp; omega)]

theorem reversal_moves (x y : List Value) (argc : Nat) (total : x.length + y.length = argc) :
    ∀ i, (x ++ y.reverse)[argMap (reversal argc y.length) i]? = (x ++ y)[i]? := by
  intro i
  have entry := reversal_entry argc y.length i (by omega)
  simp only [argMap, List.getD_eq_getElem?_getD, entry]
  by_cases first : i < x.length
  · simp only [show i < argc - y.length by omega, ite_true, Option.getD_some]
    rw [List.getElem?_append_left first, List.getElem?_append_left first]
  · simp only [show ¬ i < argc - y.length by omega, ite_false]
    by_cases second : i < argc
    · simp only [second, ite_true, Option.getD_some]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_reverse (by omega)]
      congr 1
      omega
    · simp only [second, ite_false, Option.getD_none]
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem enterFrame_args (b : CIL.Method) (vectors : b.vectorArgs = []) (parameters : b.parameterHomes = [])
    (a a' : List Value) (m : Memory) : enterFrame b a m = enterFrame b a' m := by
  simp [enterFrame, vectors, parameters, makeArgumentHomes, makeParameterHomes]

theorem position_skips (edits : List (Nat × Edit)) (pc : Nat) :
    ∀ count, skipsAfter edits pc count = true → position edits (pc + 1 + count) = position edits (pc + 1) := by
  intro count
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
    intro skips
    simp only [skipsAfter, Bool.and_eq_true, beq_iff_eq] at skips
    have unfold : position edits (pc + 1 + count + 1) =
        position edits (pc + 1 + count) + (editAt edits (pc + 1 + count)).size := rfl
    rw [show pc + 1 + (count + 1) = pc + 1 + count + 1 by omega, unfold,
      show pc + 1 + count = pc + count + 1 by omega, skips.1,
      show pc + count + 1 = pc + 1 + count by omega, ih skips.2]
    rfl

/-- Reduces a body clause of `Expansion` to a code equality the kernel can decide. -/
theorem body_of_code {Q : CIL.Program} {index : Nat} {b q : CIL.Method} {edits : List (Nat × Edit)}
    {μ σ : Nat → Nat} (found : Q[index]? = some q) (shape : q = { b with code := q.code })
    (code : expand edits μ σ b.code = q.code) : Q[index]? = some { b with code := expand edits μ σ b.code } := by
  rw [found, code, ← shape]

/-- Every successful source run is reproduced by the expanded program. -/
theorem simulate {P Q : CIL.Program} {μ : Nat → Nat} {E : Nat → List (Nat × Edit)} {perm : Nat → List Nat}
    (X : Expansion P Q μ E perm) :
    ∀ n fuel, fuel ≤ n → ∀ m b pc args args' frame stack mem r, P[m]? = some b → editAt (E m) pc ≠ .skip →
      (∀ i, args'[argMap (perm m) i]? = args[i]?) →
      run P fuel m pc args frame stack mem = .ok r →
      ∃ f, run Q f (μ m) (position (E m) pc) args' frame stack mem = .ok r := by
  intro n
  induction n with
  | zero =>
    intro fuel bound m b pc args args' frame stack mem r found notSkip moved ran
    have : fuel = 0 := by omega
    subst this
    simp [run] at ran
  | succ n ih =>
    intro fuel bound m b pc args args' frame stack mem r found notSkip moved ran
    cases fuel with
    | zero => simp [run] at ran
    | succ k =>
    have small : k ≤ n := by omega
    have foundQ := X.body m b found
    have static := X.static m b found
    cases ho : b.code[pc]? with
    | none => simp [run, found, ho] at ran
    | some op =>
    have okEdit := checkCode_at (X.checked m b found) ho
    cases hs : step b op pc args frame stack mem with
    | error fault => simp [run, found, ho, hs, Except.mapError, Bind.bind, Except.bind] at ran
    | ok action =>
    cases he : editAt (E m) pc with
    | skip => exact absurd he notSkip
    | keep =>
      simp only [editOk, he, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at okEdit
      obtain ⟨⟨⟨plain, direct⟩, targetsOk⟩, nextOk⟩ := okEdit
      have fetchQ : ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc]? =
          some (relabel (position (E m)) μ (argMap (perm m)) op) := by
        have := expand_fetch (E m) μ (argMap (perm m)) b.code pc op ho 0 (by simp [he, Edit.size])
        simpa [chunk, he] using this
      have nextPos : position (E m) (pc + 1) = position (E m) pc + 1 := by simp [position, he, Edit.size]
      have stepQ := step_relabel b { b with code := expand (E m) μ (argMap (perm m)) b.code } rfl rfl static static op plain pc
        (position (E m) pc) (position (E m)) μ (argMap (perm m)) nextPos args args' moved frame stack mem action hs
      cases action with
      | next t s fr m' =>
        rw [run_next found ho hs] at ran
        have target : editAt (E m) t ≠ .skip := by
          rcases step_target b static op plain pc args frame stack mem t s fr m' hs with same | member
          · subst same; exact nextOk
          · exact targetsOk t member
        obtain ⟨f, ranQ⟩ := ih k small m b t args args' fr s m' r found target moved ran
        exact ⟨f + 1, by rw [run_next foundQ fetchQ stepQ]; exact ranQ⟩
      | returned vals m' =>
        refine ⟨k + 1, ?_⟩
        simp only [run, found, ho, hs, Except.mapError, Bind.bind, Except.bind] at ran
        simp only [run, foundQ, fetchQ, stepQ, FrameAction.relabel, Except.mapError, Bind.bind, Except.bind]
        revert ran
        cases List.mapM (checkedValue (leaveFrame frame m')) vals <;> simp
      | call c a rest m' =>
        simp only [run, found, ho, hs, Except.mapError, Bind.bind, Except.bind] at ran
        cases hc : P[c]? with
        | none => simp [hc] at ran
        | some cb =>
        simp only [hc] at ran
        cases hen : enterFrame cb a m' with
        | error e => simp [hen] at ran
        | ok entered =>
        obtain ⟨cf, m1⟩ := entered
        simp only [hen] at ran
        cases hr : run P k c 0 a cf [] m1 with
        | error e => simp [hr] at ran
        | ok child =>
        obtain ⟨m2, res⟩ := child
        simp only [hr] at ran
        obtain ⟨n, rfl⟩ := call_op b op plain pc args frame stack mem c a rest m' hs
        simp only [directCall, beq_iff_eq] at direct
        obtain ⟨f1, childQ⟩ := ih k small c cb 0 a a cf [] m1 (m2, res) hc (checkCode_entry (X.checked c cb hc))
          (by simp [direct, argMap]) hr
        obtain ⟨f2, contQ⟩ := ih k small m b (pc + 1) args args' frame (res ++ rest) m2 r found nextOk moved ran
        rw [nextPos] at contQ
        have childQ' := run_mono Q f1 f2 _ _ _ _ _ _ _ (ready := by simp [Settled]) (h := childQ)
        have contQ' := run_mono Q f2 f1 _ _ _ _ _ _ _ (ready := by simp [Settled]) (h := contQ)
        rw [Nat.add_comm f2 f1] at contQ'
        refine ⟨f1 + f2 + 1, ?_⟩
        simp only [position] at childQ'
        simp only [run, foundQ, fetchQ, stepQ, FrameAction.relabel, X.body c cb hc, enterFrame_code, hen,
          childQ', contQ', Except.mapError, Bind.bind, Except.bind]
      | construct c a rest fr t kind m' =>
        exact (no_construct b op plain pc args frame stack mem _ _ _ _ _ _ _ hs).elim
    | dup =>
      simp only [editOk, he, Bool.and_eq_true, bne_iff_ne, ne_eq] at okEdit
      obtain ⟨feat, nextOk⟩ := okEdit
      cases op with
      | feature x =>
        rw [feature_step] at hs
        simp only [Except.ok.injEq] at hs
        subst hs
        rw [run_next found ho (feature_step b x pc args frame stack mem)] at ran
        obtain ⟨f, ranQ⟩ := ih k small m b (pc + 1) args args' frame _ mem r found nextOk moved ran
        have nextPos : position (E m) (pc + 1) = position (E m) pc + 1 + 1 + 1 := by
          simp [position, he, Edit.size]
        rw [nextPos] at ranQ
        have f0 : ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc]? =
            some (.feature x) := by
          simpa [chunk, he] using expand_fetch (E m) μ (argMap (perm m)) b.code pc _ ho 0 (by simp [he, Edit.size])
        have f1 : ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc + 1]? =
            some (.feature x) := by
          simpa [chunk, he] using expand_fetch (E m) μ (argMap (perm m)) b.code pc _ ho 1 (by simp [he, Edit.size])
        have f2 : ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc + 1 + 1]? =
            some .band := by
          simpa [chunk, he] using expand_fetch (E m) μ (argMap (perm m)) b.code pc _ ho 2 (by simp [he, Edit.size])
        refine ⟨f + 1 + 1 + 1, ?_⟩
        rw [run_next foundQ f0 (feature_step _ x _ args' frame stack mem),
          run_next foundQ f1 (feature_step _ x _ args' frame _ mem),
          run_next foundQ f2 (band_same_step _ _ _ args' frame stack mem)]
        exact ranQ
      | _ => simp [isFeature] at feat
    | call h =>
      simp only [editOk, he, bne_iff_ne, ne_eq] at okEdit
      obtain ⟨i, codeAt, helper⟩ := X.calls m b found pc h (editAt_mem he (by simp))
      rw [ho] at codeAt
      cases codeAt
      obtain ⟨x, y, rest, value, rfl, nx, ny, available, intrinsic, nv, rfl⟩ :=
        intrinsic_two_step b i pc args frame stack mem _ hs
      rw [run_next found ho hs] at ran
      obtain ⟨f, ranQ⟩ := ih k small m b (pc + 1) args args' frame _ mem r found okEdit moved ran
      have nextPos : position (E m) (pc + 1) = position (E m) pc + 1 := by simp [position, he, Edit.size]
      rw [nextPos] at ranQ
      have fetchQ : ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc]? =
          some (.call h 2) := by
        simpa [chunk, he] using expand_fetch (E m) μ (argMap (perm m)) b.code pc _ ho 0 (by simp [he, Edit.size])
      obtain ⟨final, vals⟩ := r
      exact run_call_exists foundQ fetchQ (call_two_step _ h _ args' frame x y rest mem nx ny)
        ⟨5, call_helper_invoke mem helper available nx ny intrinsic nv⟩ ⟨f, ranQ⟩
    | fold h =>
      simp only [editOk, he, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at okEdit
      obtain ⟨skipNext, nextOk⟩ := okEdit
      obtain ⟨c, i, codeAt, codeNext, helper⟩ := X.folds m b found pc h (editAt_mem he (by simp))
      rw [ho] at codeAt
      cases codeAt
      rw [run_next found ho (const_step b c pc args frame stack mem)] at ran
      cases k with
      | zero => simp [run] at ran
      | succ k' =>
      cases hs2 : step b (.intrinsic i 3) (pc + 1) args frame (.scalar (.i32 c) :: stack) mem with
      | error e => simp [run, found, codeNext, hs2, Except.mapError, Bind.bind, Except.bind] at ran
      | ok act =>
      obtain ⟨x, y, rest, value, rfl, nx, ny, available, intrinsic, nv, rfl⟩ :=
        intrinsic_three_step b i c (pc + 1) args frame stack mem act hs2
      rw [run_next found codeNext hs2] at ran
      obtain ⟨f, ranQ⟩ := ih k' (by omega) m b (pc + 1 + 1) args args' frame _ mem r found nextOk moved ran
      have nextPos : position (E m) (pc + 1 + 1) = position (E m) pc + 1 := by
        simp [position, he, skipNext, Edit.size]
      rw [nextPos] at ranQ
      have fetchQ : ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc]? =
          some (.call h 2) := by
        simpa [chunk, he] using expand_fetch (E m) μ (argMap (perm m)) b.code pc _ ho 0 (by simp [he, Edit.size])
      obtain ⟨final, vals⟩ := r
      exact run_call_exists foundQ fetchQ (call_two_step _ h _ args' frame x y rest mem nx ny)
        ⟨6, fold_helper_invoke mem helper available nx ny intrinsic nv⟩ ⟨f, ranQ⟩
    | reverse locals callee argc =>
      simp only [editOk, he, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq] at okEdit
      obtain ⟨⟨⟨⟨⟨pushes, callAt⟩, skips⟩, nextOk⟩, fits⟩, permCallee⟩ := okEdit
      have callFetch := isCall_eq callAt
      obtain ⟨pairs, names, _, steps, ranCall⟩ :=
        pushes_source found args frame mem r locals pc (k + 1) stack pushes ran
      have count : pairs.length = locals.length := by rw [← names, List.length_map]
      generalize hvalues : pairs.map Prod.snd = values at ranCall
      have valuesLength : values.length = locals.length := by rw [← hvalues, List.length_map, count]
      cases hk : k + 1 - locals.length with
      | zero => rw [hk] at ranCall; simp [run] at ranCall
      | succ k2 =>
      rw [hk] at ranCall
      cases hs2 : step b (.call callee argc) (pc + locals.length) args frame (values.reverse ++ stack) mem with
      | error e => simp [run, found, callFetch, hs2, Except.mapError, Bind.bind, Except.bind] at ranCall
      | ok act =>
      obtain ⟨long, a, checkedA, rfl⟩ := call_step_ok hs2
      simp only [run, found, callFetch, hs2, Except.mapError, Bind.bind, Except.bind] at ranCall
      cases hc : P[callee]? with
      | none => simp [hc] at ranCall
      | some cb =>
      simp only [hc] at ranCall
      cases hen : enterFrame cb a mem with
      | error e => simp [hen] at ranCall
      | ok entered =>
      obtain ⟨cf, m1⟩ := entered
      simp only [hen] at ranCall
      cases hr : run P k2 callee 0 a cf [] m1 with
      | error e => simp [hr] at ranCall
      | ok child =>
      obtain ⟨m2, res⟩ := child
      simp only [hr] at ranCall
      simp only [List.length_append, List.length_reverse, valuesLength] at long
      have takeP : (values.reverse ++ stack).take argc = values.reverse ++ stack.take (argc - locals.length) := by
        rw [List.take_append, List.take_of_length_le (by simp [valuesLength]; omega)]
        simp [valuesLength]
      have takeQ : (values ++ stack).take argc = values ++ stack.take (argc - locals.length) := by
        rw [List.take_append, List.take_of_length_le (by simp [valuesLength]; omega)]
        simp [valuesLength]
      have dropP : (values.reverse ++ stack).drop argc = stack.drop (argc - locals.length) := by
        rw [List.drop_append, List.drop_of_length_le (by simp [valuesLength]; omega)]
        simp [valuesLength]
      have dropQ : (values ++ stack).drop argc = stack.drop (argc - locals.length) := by
        rw [List.drop_append, List.drop_of_length_le (by simp [valuesLength]; omega)]
        simp [valuesLength]
      rw [takeP, List.reverse_append, List.reverse_reverse] at checkedA
      obtain ⟨front, back, frontOk, backOk, rfl⟩ := mapM_append_ok checkedA
      have checkedQ : ((values ++ stack).take argc).reverse.mapM (checkedValue mem) = .ok (front ++ back.reverse) := by
        rw [takeQ, List.reverse_append]
        exact mapM_append_of frontOk (mapM_reverse_ok backOk)
      have frontLength : front.length = argc - locals.length := by
        rw [mapM_length frontOk, List.length_reverse, List.length_take]
        omega
      have backLength : back.length = locals.length := by rw [mapM_length backOk, valuesLength]
      have related : ∀ i, (front ++ back.reverse)[argMap (perm callee) i]? = (front ++ back)[i]? := by
        rw [permCallee, ← backLength]
        exact reversal_moves front back argc (by omega)
      obtain ⟨f1, childQ⟩ := ih k2 (by omega) callee cb 0 (front ++ back) (front ++ back.reverse) cf [] m1 (m2, res) hc
        (checkCode_entry (X.checked callee cb hc)) related hr
      rw [dropP] at ranCall
      obtain ⟨f2, contQ⟩ := ih k2 (by omega) m b (pc + locals.length + 1) args args' frame
        (res ++ stack.drop (argc - locals.length)) m2 r found nextOk moved ranCall
      have nextPos : position (E m) (pc + locals.length + 1) = position (E m) pc + locals.length + 1 := by
        rw [show pc + locals.length + 1 = pc + 1 + locals.length by omega, position_skips (E m) pc _ skips]
        simp [position, he, Edit.size]
        omega
      rw [nextPos] at contQ
      have childQ' := run_mono Q f1 f2 _ _ _ _ _ _ _ (ready := by simp [Settled]) (h := childQ)
      have contQ' := run_mono Q f2 f1 _ _ _ _ _ _ _ (ready := by simp [Settled]) (h := contQ)
      rw [Nat.add_comm f2 f1] at contQ'
      simp only [position] at childQ'
      have chunkAt : ∀ j, j < locals.length + 1 → ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc + j]? =
          (locals.reverse.map (fun l => CIL.Op.local l none) ++ [.call (μ callee) argc])[j]? := by
        intro j small
        have := expand_fetch (E m) μ (argMap (perm m)) b.code pc _ ho j (by simp [he, Edit.size]; omega)
        simpa [chunk, he] using this
      have callQ : ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc + locals.length]? = some (.call (μ callee) argc) := by
        rw [chunkAt locals.length (by omega), List.getElem?_append_right (by simp)]
        simp
      have pushCodes : ∀ j, j < pairs.reverse.length → ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method).code[position (E m) pc + j]? =
          (pairs.reverse.map fun x => CIL.Op.local x.1 none)[j]? := by
        intro j small
        rw [chunkAt j (by simp at small; omega), List.getElem?_append_left (by simp at small ⊢; omega), ← names]
        simp only [List.map_reverse, List.map_map]
        rfl
      have stepCall : step ({ b with code := expand (E m) μ (argMap (perm m)) b.code } : CIL.Method) (.call (μ callee) argc) (position (E m) pc + locals.length) args' frame
          (values ++ stack) mem = .ok (.call (μ callee) (front ++ back.reverse) (stack.drop (argc - locals.length)) mem) := by
        rw [← dropQ]
        exact call_step_of (by simp [valuesLength]; omega) checkedQ
      have enterQ : enterFrame { cb with code := expand (E callee) μ (argMap (perm callee)) cb.code }
          (front ++ back.reverse) mem = .ok (cf, m1) := by
        rw [enterFrame_code, enterFrame_args cb (X.frames callee cb hc).1 (X.frames callee cb hc).2 _ (front ++ back)]
        exact hen
      refine ⟨f1 + f2 + 1 + pairs.reverse.length, ?_⟩
      rw [pushes_target foundQ args' frame mem pairs.reverse (position (E m) pc) (f1 + f2 + 1) stack pushCodes
        (fun x member pc' stack' => steps x (List.mem_reverse.mp member) _ pc' args' stack')]
      have stackQ : (pairs.reverse.map Prod.snd).reverse ++ stack = values ++ stack := by
        simp [← hvalues, List.map_reverse]
      rw [stackQ, List.length_reverse, count]
      simp only [run, foundQ, callQ, stepCall, X.body callee cb hc, enterQ, childQ', contQ', Except.mapError,
        Bind.bind, Except.bind]

/-- Invocation certificates carry over from the source program to its expansion. -/
theorem certificate_transfer {P Q : CIL.Program} {μ : Nat → Nat} {E : Nat → List (Nat × Edit)}
    {perm : Nat → List Nat} (X : Expansion P Q μ E perm) {m : Nat} (direct : perm m = [])
    {args : List Value} {initial final : Memory} {fuel : Nat}
    {values : List Value} (wellFormed : initial.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors Q) initial)
    (certificate : InvocationCertificate P m args initial fuel final values) :
    ∃ fuel', InvocationCertificate Q (μ m) args initial fuel' final values := by
  obtain ⟨_, body, frame, entered, found, checked, setup, ran, _⟩ := certificate
  obtain ⟨f, ranQ⟩ := simulate X fuel fuel (Nat.le_refl _) m body 0 args args frame [] entered (final, values) found
    (checkCode_entry (X.checked m body found)) (by simp [direct, argMap]) ran
  have setupQ : enterFrame { body with code := expand (E m) μ (argMap (perm m)) body.code } args initial =
      .ok (frame, entered) := by
    rw [enterFrame_code]; exact setup
  exact ⟨f, certify_invocation Q (μ m) _ args initial frame entered f final values (X.body m body found) checked
    setupQ (checked_entry_live_state Q _ args args initial entered frame wellFormed world checked setupQ) ranQ⟩

/-- A wrapping contract carries over to an expansion with the same static world. -/
theorem wrapping_transfer {P Q : CIL.Program} {μ : Nat → Nat} {E : Nat → List (Nat × Edit)}
    {perm : Nat → List Nat} (X : Expansion P Q μ E perm)
    (descriptors : programStaticDescriptors Q = programStaticDescriptors P)
    {operation : BitVec 256 → BitVec 256 → BitVec 256} {entry : Nat} (direct : perm entry = [])
    (proof : WrappingBinaryContract operation P entry) : WrappingBinaryContract operation Q (μ entry) := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, post⟩ := proof memory left right output ⟨call.1, descriptors ▸ call.2⟩
  obtain ⟨f, certificateQ⟩ := certificate_transfer X direct call.1.1 call.2 certificate
  exact ⟨f, final, certificateQ, post⟩

/-- A reporting contract carries over to an expansion with the same static world. -/
theorem reporting_transfer {P Q : CIL.Program} {μ : Nat → Nat} {E : Nat → List (Nat × Edit)}
    {perm : Nat → List Nat} (X : Expansion P Q μ E perm)
    (descriptors : programStaticDescriptors Q = programStaticDescriptors P)
    {operation : BitVec 256 → BitVec 256 → BitVec 256} {flag : BitVec 256 → BitVec 256 → Bool} {entry : Nat}
    (direct : perm entry = []) (proof : ReportingBinaryContract operation flag P entry) :
    ReportingBinaryContract operation flag Q (μ entry) := by
  intro memory left right output call
  obtain ⟨fuel, final, certificate, post⟩ := proof memory left right output ⟨call.1, descriptors ▸ call.2⟩
  obtain ⟨f, certificateQ⟩ := certificate_transfer X direct call.1.1 call.2 certificate
  exact ⟨f, final, certificateQ, post⟩

end UInt256Model.Safety.CodeExpansion

-- Lets the kernel compare expanded bodies with extracted ones by evaluation.
deriving instance DecidableEq for CIL.MemoryOp
deriving instance DecidableEq for CIL.Op

namespace UInt256Model.Safety.CodeExpansion

#print axioms simulate
#print axioms wrapping_transfer
#print axioms reporting_transfer

end UInt256Model.Safety.CodeExpansion
