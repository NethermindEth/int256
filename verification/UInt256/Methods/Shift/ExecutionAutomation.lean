import UInt256.Methods.Shift.Storage
import UInt256.Methods.Shift.Count
import UInt256.Methods.Shift.WholeShift
import UInt256.Methods.Shift.Representation

open CIL UInt256Model

namespace UInt256Proof.Shift

/-- Shared checked execution for the partial-word routes in either direction.
    Each caller retains its own mathematical result and count-case hypothesis. -/
macro "shift_word_case " memory:term ", " input:term ", " output:term ", " limbs:term
    ", " reads:term " with " facts:term,+ : tactic => `(tactic|
  (obtain ⟨h0, h1, h2, h3⟩ := limb_reads $memory $input $limbs $reads
   have h8 : (0 : Int) ≤ ($output : Int) + 8 := by omega
   have h16 : (0 : Int) ≤ ($output : Int) + 16 := by omega
   have h24 : (0 : Int) ≤ ($output : Int) + 24 := by omega
   have ha8 : (($output : Int) + 8).toNat = $output + 8 := by omega
   have ha16 : (($output : Int) + 16).toNat = $output + 16 := by omega
   have ha24 : (($output : Int) + 24).toNat = $output + 24 := by omega
   cil_execute_core h0, h1, h2, h3, mask_count, carry_count_mask,
     nat_mask_count, nat_carry_count, h8, h16, h24, evalMemory, eval_create256,
     eval_store256, unsafeAsRef, unsafeAdd, offsetValue, $[$facts:term],* with
       (first | cil_shift_store_call | cil_store_call)
   all_goals intro address
   all_goals simp [*, store4, nat_carry_count_flat]))

/-- Returning operators use private output homes and retain all caller bytes. -/
macro "shift_value_case " memory:term ", " input:term ", " limbs:term ", " reads:term
    " with " facts:term,+ : tactic => `(tactic|
  (obtain ⟨h0, h1, h2, h3⟩ := limb_reads $memory $input $limbs $reads
   cil_execute_core h0, h1, h2, h3, mask_count, carry_count_mask,
     nat_mask_count, nat_carry_count, evalMemory, eval_create256, eval_store256,
     unsafeAsRef, unsafeAdd, offsetValue, $[$facts:term],* with
       (first | cil_shift_store_home_call)
   all_goals simp [*, nat_carry_count_flat]))

macro "shift_zero_output " count:term ", " outside:term ", " zero:term : tactic => `(tactic|
  (have outsideNormalized : ¬ ($count).sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using ($outside)
   rcases ($zero) with positive | multiple
   · have positiveNormalized : (0 : Int) ≤ ($count).toInt >>> 6 := by simpa only [BitVec.toInt_sshiftRight] using positive
     cil_execute_core outsideNormalized, positiveNormalized, evalMemory, write256 with (first | cil_shift_store_call | cil_store_call)
     all_goals intro address
     all_goals simp only [writeBytes_write_local, write_local_read_byte]
   · change ($count) &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 0 at multiple
     by_cases positiveNormalized : (0 : Int) ≤ ($count).toInt >>> 6
     all_goals cil_execute_core outsideNormalized, multiple, positiveNormalized, evalMemory, write256 with (first | cil_shift_store_call | cil_store_call)
     all_goals intro address
     all_goals simp only [writeBytes_write_local, write_local_read_byte]))

macro "shift_zero_value " count:term ", " outside:term ", " zero:term : tactic => `(tactic|
  (have outsideNormalized : ¬ ($count).sshiftRight 6 < BitVec.ofNat 32 4 := by simpa [BitVec.lt_def] using ($outside)
   rcases ($zero) with positive | multiple
   · have positiveNormalized : (0 : Int) ≤ ($count).toInt >>> 6 := by simpa only [BitVec.toInt_sshiftRight] using positive
     cil_execute_core outsideNormalized, positiveNormalized, eval_init_home, aggregate_snapshot_after_write, writeAggregate_caller, evalMemory, write256 with (first | cil_shift_store_home_call)
     all_goals simp only [write_local_read_byte]
   · change ($count) &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 0 at multiple
     by_cases positiveNormalized : (0 : Int) ≤ ($count).toInt >>> 6
     all_goals cil_execute_core outsideNormalized, multiple, positiveNormalized, eval_init_home, aggregate_snapshot_after_write, writeAggregate_caller, evalMemory, write256 with (first | cil_shift_store_home_call)
     all_goals simp only [write_local_read_byte]))

end UInt256Proof.Shift
