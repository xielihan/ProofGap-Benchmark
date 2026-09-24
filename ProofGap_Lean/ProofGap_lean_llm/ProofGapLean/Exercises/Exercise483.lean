import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise483

noncomputable section

def original (a x : ℝ) : ℝ := (Real.cos x - Real.cos a) / (x - a)
def transformed (a x : ℝ) : ℝ :=
  -(Real.sin ((x - a) / 2) / ((x - a) / 2)) * Real.sin ((x + a) / 2)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 483, gap 1. -/
private theorem original_eq_transformed {a x : ℝ} :
    original a x = transformed a x := by
  have hx : (x + a) / 2 + (x - a) / 2 = x := by
    ring
  have ha : (x + a) / 2 - (x - a) / 2 = a := by
    ring
  have hcos :
      Real.cos x - Real.cos a =
        -2 * Real.sin ((x + a) / 2) * Real.sin ((x - a) / 2) := by
    calc
      Real.cos x - Real.cos a =
          Real.cos ((x + a) / 2 + (x - a) / 2) -
            Real.cos ((x + a) / 2 - (x - a) / 2) := by
              rw [hx, ha]
      _ = -2 * Real.sin ((x + a) / 2) * Real.sin ((x - a) / 2) := by
        rw [Real.cos_add, Real.cos_sub]
        ring
  unfold original transformed
  rw [hcos]
  field_simp

theorem gap1 (a L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (transformed a) a L := by
  have h_eq : original a = transformed a := by
    funext x
    exact original_eq_transformed
  unfold HasLimitAt
  rw [h_eq]

/-- Exercise 483, gap 2. -/
theorem gap2 (a : ℝ) : HasLimitAt (transformed a) a (-Real.sin a) := by
  refine (gap1 a (-Real.sin a)).mp ?_
  have hslope : slope Real.cos a = original a := by
    funext x
    simp only [slope, original, div_eq_mul_inv, vsub_eq_sub, smul_eq_mul]
    ring
  unfold HasLimitAt
  rw [← hslope]
  exact (Real.hasDerivAt_cos a).tendsto_slope

/-- Exercise 483, gap 3. -/
theorem gap3 (a : ℝ) : HasLimitAt (original a) a (-Real.sin a) := by
  exact (gap1 a (-Real.sin a)).mpr (gap2 a)

end

end ProofGap.Exercise483
