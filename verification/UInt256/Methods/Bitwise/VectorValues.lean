import UInt256.Safety.ArgumentValues
import UInt256.Methods.Bitwise.ScalarSafetyContract
import CIL.Safety.ValueBitCasts
import CIL.Safety.CallComposition

namespace UInt256Proof.Bitwise.VectorValues
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise

theorem aggregate_to_vector (bits : BitVec 256) :
    bitcastValue (.aggregate 32) .vector256 (.aggregate (numberBytes bits.toNat 32)) = .ok (.v256 bits) := by
  have length : (numberBytes bits.toNat 32).length = 32 := by simp [numberBytes]
  simp [bitcastValue, CIL.Value.hasUnspecified, valueSnapshot, snapshotValue, CIL.SnapshotShape.width,
    length, List.map_map, Function.comp_def, byteNumber_numberBytes, Pure.pure, Except.pure]
  rw [Nat.mod_eq_of_lt bits.isLt]
  simp

theorem vector_to_aggregate (bits : BitVec 256) :
    bitcastValue .vector256 (.aggregate 32) (.v256 bits) = .ok (.aggregate (numberBytes bits.toNat 32)) := by
  simp [bitcastValue, CIL.Value.hasUnspecified, valueSnapshot, snapshotValue, CIL.SnapshotShape.width,
    List.map_map, Function.comp_def, Pure.pure, Except.pure]

#print axioms aggregate_to_vector
#print axioms vector_to_aggregate
end UInt256Proof.Bitwise.VectorValues
