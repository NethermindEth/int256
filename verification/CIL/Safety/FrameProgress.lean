import CIL.Safety.HomeProgress

namespace CIL.Safety

/-- Metadata/type compatibility, independent of caller memory and execution.
    Unknown initializers remain unknown; numeric initializers must fit their
    physical home, and a managed root may start null. -/
def InitializerFits (kind : CIL.LocalKind) (initial : CIL.Value) : Prop :=
  initial = .unmodeled ∨ match kind, initial with
  | .reference, .nullRef => True
  | .byte, .i32 bits => bits.toNat < 256
  | .word32, .i32 _ | .word64, .i64 _ | .vector128, .v128 _ | .vector256, .v256 _ => True
  | _, _ => False

theorem initializer_numeric_number {kind : CIL.LocalKind} {initial : CIL.Value}
    (fits : InitializerFits kind initial) (numeric : kind ≠ .reference)
    (known : initial ≠ .unmodeled) : ∃ number, localNumber kind initial = .ok number := by
  cases kind <;> cases initial <;> simp_all [InitializerFits, localNumber]

theorem localWidth_bounded (kind : CIL.LocalKind) : localWidth kind < nativeLimit := by
  cases kind <;> simp [localWidth, nativeLimit]

theorem makeLocal_succeeds (m : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (wellFormed : m.WellFormed) (fits : InitializerFits kind initial) :
    ∃ slot owned result, makeLocal activation kind initial m = .ok (slot, owned, result) := by
  by_cases root : kind = .reference
  · subst kind
    cases initial <;> simp_all [InitializerFits, makeLocal]
  · obtain ⟨reference, memory, home⟩ :=
      allocateHome_succeeds m activation (localWidth kind) wellFormed (localWidth_bounded kind)
    by_cases unknown : initial = .unmodeled
    · refine ⟨.bytes kind reference, [reference.allocation], memory, ?_⟩
      cases kind <;> simp_all [makeLocal, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · obtain ⟨number, value⟩ := initializer_numeric_number fits root unknown
      obtain ⟨slot, result, stored⟩ := fresh_home_storeLocal_succeeds _ _ _ _ _ _ _ home value
      refine ⟨slot, [reference.allocation], result, ?_⟩
      cases kind <;> simp_all [makeLocal, Bind.bind, Except.bind, Pure.pure, Except.pure]

def InitializersFit : List CIL.LocalKind → List CIL.Value → Prop
  | [], [] => True
  | kind :: kinds, initial :: initializers => InitializerFits kind initial ∧ InitializersFit kinds initializers
  | _, _ => False

theorem makeLocals_succeeds (m : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value) (wellFormed : m.WellFormed)
    (fits : InitializersFit kinds initializers) :
    ∃ slots owned result, makeLocals activation kinds initializers m = .ok (slots, owned, result) := by
  induction kinds generalizing m initializers with
  | nil =>
    cases initializers with
    | nil => exact ⟨[], [], m, rfl⟩
    | cons initial rest => cases fits
  | cons kind kinds ih =>
    cases initializers with
    | nil => cases fits
    | cons initial initials =>
      obtain ⟨slot, ids, memory, prepared⟩ := makeLocal_succeeds m activation _ _ wellFormed fits.1
      have valid := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed prepared
      obtain ⟨slots, other, result, rest⟩ := ih memory initials valid fits.2
      exact ⟨slot :: slots, ids ++ other, result, by
        simp [makeLocals, prepared, rest, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- Aggregate-home indices must designate actual by-value aggregate arguments.
    This is signature/type compatibility, not an access or future-run condition. -/
def AggregateArgumentsFit (indices : List Nat) (args : List Value) : Prop :=
  ∀ index ∈ indices, ∃ bits, args[index]? = some (.scalar (.v256 bits))

theorem makeArgumentHomes_succeeds (m : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (wellFormed : m.WellFormed) (fits : AggregateArgumentsFit indices args) :
    ∃ homes owned result, makeArgumentHomes activation indices args m = .ok (homes, owned, result) := by
  induction indices generalizing m with
  | nil => exact ⟨[], [], m, rfl⟩
  | cons index indices ih =>
    obtain ⟨bits, argument⟩ := fits index (by simp)
    obtain ⟨reference, memory, home⟩ :=
      allocateHome_succeeds m activation (localWidth .vector256) wellFormed (localWidth_bounded _)
    obtain ⟨slot, stored, store⟩ := fresh_home_storeLocal_succeeds m memory activation .vector256 reference (.v256 bits) bits.toNat home rfl
    have valid := storeLocal_preserves_wellFormed _ _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ wellFormed home) store
    obtain ⟨homes, owned, result, rest⟩ := ih stored valid (fun i member => fits i (by simp [member]))
    exact ⟨(index, slot) :: homes, reference.allocation :: owned, result, by
      simp [makeArgumentHomes, argument, home, store, rest,
        Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

def FrameSetupFits (body : CIL.Method) (args : List Value) : Prop :=
  InitializersFit body.localKinds body.locals ∧ AggregateArgumentsFit body.aggregateArgs args

theorem enterFrame_succeeds (body : CIL.Method) (args : List Value) (m : Memory)
    (wellFormed : m.WellFormed) (fits : FrameSetupFits body args) :
    ∃ frame memory, enterFrame body args m = .ok (frame, memory) := by
  obtain ⟨locals, owned, memory, prepared⟩ :=
    makeLocals_succeeds m m.nextIdentity body.localKinds body.locals wellFormed fits.1
  have valid := makeLocals_preserves_wellFormed _ _ _ _ _ _ _ wellFormed prepared
  obtain ⟨arguments, ids, result, homes⟩ :=
    makeArgumentHomes_succeeds memory m.nextIdentity body.aggregateArgs args valid fits.2
  exact ⟨⟨m.nextIdentity, locals, owned ++ ids, arguments⟩, result, by
    simp [enterFrame, prepared, homes, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

theorem enterFrame_live_succeeds (program : CIL.Program) (body : CIL.Method)
    (args : List Value) (m : Memory) (wellFormed : m.WellFormed) (valid : ValuesValid m args)
    (world : StaticWorldValid (programStaticDescriptors program) m) (fits : FrameSetupFits body args) :
    ∃ frame memory, enterFrame body args m = .ok (frame, memory) ∧ LiveState program args frame [] memory := by
  obtain ⟨frame, memory, setup⟩ := enterFrame_succeeds body args m wellFormed fits
  exact ⟨frame, memory, setup, enterFrame_live_state _ _ _ _ _ _ wellFormed valid world setup⟩

#print axioms makeLocal_succeeds
#print axioms makeLocals_succeeds
#print axioms makeArgumentHomes_succeeds
#print axioms enterFrame_succeeds
#print axioms enterFrame_live_succeeds

end CIL.Safety
