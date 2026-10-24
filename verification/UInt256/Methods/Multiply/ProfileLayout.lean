import UInt256.Methods.Multiply.EntryContract
import UInt256.Methods.Multiply.WordHardwareSafety
import UInt256.Methods.Multiply.ProductStorageVector
import UInt256.Methods.Multiply.FullSafetyAvx512Top
import UInt256.Methods.Multiply.FullSafetyAvx2Top

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}

/-- Helper indices after an entry at `base`; vector storage has no limb helper, so the word helper moves down. -/
def profileIndices (profile : CIL.FeatureProfile) (base : Nat) : Indices :=
  bif profile.vector256Accelerated then ⟨base, base + 1, base + 2, base + 3, base + 4, base + 5, base + 6, 0, base + 7⟩
  else ⟨base, base + 1, base + 2, base + 3, base + 4, base + 5, base + 6, base + 7, base + 8⟩
def profileWordBody (profile : CIL.FeatureProfile) : CIL.Method :=
  bif profile.bmi2 then hardwareWordBody false profile
  else bif profile.armBase64 then hardwareWordBody true profile else scalarWordBody profile
def profileStorageBody (profile : CIL.FeatureProfile) (limbs : Nat) : CIL.Method :=
  bif profile.vector256Accelerated then ProductStorage.vectorBody profile else ProductStorage.body profile limbs
/-- AVX512DQ.VL top limbs also need AVX2, AVX512DQ, AVX512F and AVX512F.VL. -/
def profileTopReady (profile : CIL.FeatureProfile) : Bool :=
  !profile.avx512DQVL || (profile.avx2 && profile.avx512DQ && profile.avx512F && profile.avx512FVL)

theorem profile_storage_contract (profile : CIL.FeatureProfile) (program : CIL.Program) (index limbs : Nat)
    (found : program[index]? = some (profileStorageBody profile limbs))
    (limbsFound : program[limbs]? = bif profile.vector256Accelerated then program[limbs]? else some (LimbStorage.body profile)) :
    ProductStorage.Contract program index := by
  cases vector : profile.vector256Accelerated
  · simp only [profileStorageBody, vector, Bool.cond_false] at found limbsFound
    exact ProductStorage.scalar_contract profile vector program index limbs found limbsFound
  · simp only [profileStorageBody, vector, Bool.cond_true] at found
    exact ProductStorage.vector_contract profile vector program index found

/-- Bind the storage implementation the profile selects; without a limb helper its slot is unconstrained. -/
def profileContext (indices : Indices) (profile : CIL.FeatureProfile) (program : CIL.Program)
    (entry : program[indices.entry]? = some (multiplyBody profile indices))
    (full : program[indices.full]? = some (Full.fullBody profile indices.word indices.count indices.storage alternative))
    (leftTwo : program[indices.leftTwo]? = some (LeftTwo.leftTwoBody profile indices.word indices.count indices.storage))
    (bothTwo : program[indices.bothTwo]? = some (BothTwo.bothTwoBody profile indices.word indices.count indices.storage))
    (count : program[indices.count]? = some (CountSafety.body profile))
    (single : program[indices.single]? = some (ScalarSafety.scalarBody profile indices.word indices.storage))
    (storage : program[indices.storage]? = some (profileStorageBody profile indices.limbs))
    (limbs : program[indices.limbs]? =
      bif profile.vector256Accelerated then program[indices.limbs]? else some (LimbStorage.body profile)) :
    Context alternative :=
  ⟨indices, profile, program, entry, full, leftTwo, bothTwo, count, single,
    profile_storage_contract profile program indices.storage indices.limbs storage limbs⟩

theorem profile_word_contract (ctx : Context alternative)
    (found : ctx.program[ctx.indices.word]? = some (profileWordBody ctx.profile)) :
    Calls.WordContract ctx.program ctx.indices.word := by
  cases bmi : ctx.profile.bmi2
  · cases arm : ctx.profile.armBase64
    · simp only [profileWordBody, bmi, arm, Bool.cond_false] at found
      exact scalar_word_contract ctx found bmi arm
    · simp only [profileWordBody, bmi, arm, Bool.cond_false, Bool.cond_true] at found
      exact hardware_word_contract true ctx.profile bmi (fun _ => arm) ctx.program ctx.indices.word found
  · simp only [profileWordBody, bmi, Bool.cond_true] at found
    exact hardware_word_contract false ctx.profile bmi (fun h => nomatch h) ctx.program ctx.indices.word found

theorem profile_top_contract (ctx : Context) (ready : profileTopReady ctx.profile = true) :
    Full.FullTopContract ctx.profile ctx.program ctx.indices.full ctx.indices.word ctx.indices.count ctx.indices.storage := by
  cases vl : ctx.profile.avx512DQVL
  · cases avx2 : ctx.profile.avx2
    · exact Full.scalar_top_contract ctx.profile ctx.program _ _ _ _ ctx.full vl avx2
    · exact Full.full_avx2_top ctx.profile ctx.program _ _ _ _ ctx.full vl avx2
  · simp only [profileTopReady, vl, Bool.not_true, Bool.false_or, Bool.and_eq_true] at ready
    obtain ⟨⟨⟨avx2, dq⟩, foundation⟩, wide⟩ := ready
    exact Full.full_avx512_top ctx.profile ctx.program _ _ _ _ ctx.full vl avx2 dq foundation wide

#print axioms profile_storage_contract
#print axioms profile_word_contract
#print axioms profile_top_contract
end UInt256Proof.Multiply.Entry
