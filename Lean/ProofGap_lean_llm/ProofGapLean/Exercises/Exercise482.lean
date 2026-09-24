import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise482

noncomputable section

def original (a x : ℝ) : ℝ := (Real.sin x - Real.sin a) / (x - a)
def sumToProduct (a x : ℝ) : ℝ :=
  2 * Real.cos ((x + a) / 2) * Real.sin ((x - a) / 2) / (x - a)
def normalized (a x : ℝ) : ℝ :=
  Real.cos ((x + a) / 2) * Real.sin ((x - a) / 2) / ((x - a) / 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_482/1.txt`. -/
theorem gap1 (a L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (sumToProduct a) a L := by
  have h : original a = sumToProduct a := by
    funext x
    unfold original sumToProduct
    rw [Real.sin_sub_sin] <;> ring
  rw [h]

/-- Source: `proof_gap/exercise_482/2.txt`. -/
theorem gap2 (a L : ℝ) :
    HasLimitAt (sumToProduct a) a L ↔ HasLimitAt (normalized a) a L := by
  have h : sumToProduct a = normalized a := by
    funext x
    by_cases hx : x = a
    · subst x
      simp [sumToProduct, normalized]
    · unfold sumToProduct normalized
      field_simp [sub_ne_zero.mpr hx] <;> ring
  rw [h]

/-- Source: `proof_gap/exercise_482/3.txt`. -/
theorem gap3 (a : ℝ) : HasLimitAt (normalized a) a (Real.cos a) := by
  have horiginal : HasLimitAt (original a) a (Real.cos a) := by
    unfold HasLimitAt
    change Filter.Tendsto
      (fun x : ℝ => (Real.sin x - Real.sin a) / (x - a))
      (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (Real.cos a))
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin a).tendsto_slope
  exact (gap2 a (Real.cos a)).mp
    ((gap1 a (Real.cos a)).mp horiginal)

/-- Source: `proof_gap/exercise_482/4.txt`. -/
theorem gap4 (a : ℝ) : HasLimitAt (original a) a (Real.cos a) := by
  exact (gap1 a (Real.cos a)).mpr
    ((gap2 a (Real.cos a)).mpr (gap3 a))

end

end ProofGap.Exercise482
