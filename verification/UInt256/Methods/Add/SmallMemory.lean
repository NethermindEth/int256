import UInt256.Methods.Add.Bindings
import CIL.Safety.NumericHomes

/-! Arguments and frame setup of the extracted small-addition helper. -/

namespace UInt256Proof.Safety

open CIL.Safety

def smallArguments (input output : Reference) (word : BitVec 64) : List Value :=
  [.reference (.address input), .scalar (.i64 word), .reference (.address output)]

/-- The numeric home of one extracted local, when its initializer fits its kind. -/
def numericSpec? (kind : CIL.LocalKind) (value : CIL.Value) : Option NumericLocalSpec :=
  match fits : localNumber kind value with
  | .ok number => some ⟨kind, value, number, fits⟩
  | .error _ => none

/-- Home recipe read from the extracted locals; the setup equations reject any other local. -/
def smallLocalSpecs : List NumericLocalSpec :=
  (Extracted.addScalarUInt64Body.localKinds.zip Extracted.addScalarUInt64Body.locals).filterMap
    fun entry => numericSpec? entry.1 entry.2

/-- Entry allocates one initialized writable home per local without changing caller memory. -/
theorem small_frame_setup (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame entered,
      enterFrame Extracted.addScalarUInt64Body args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity smallLocalSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup Extracted.addScalarUInt64Body smallLocalSpecs (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) memory args wellFormed

end UInt256Proof.Safety
