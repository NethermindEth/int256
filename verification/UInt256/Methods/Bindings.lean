import Extracted
import CIL.ProfileEquivalence

namespace Extracted

@[cil_code] def entryIndex : Nat := 0
abbrev entryBody := method0

theorem programProfiles : program.map (·.profile) = List.replicate program.length profile := rfl

end Extracted
