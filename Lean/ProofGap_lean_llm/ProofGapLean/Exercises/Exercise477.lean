import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise477

noncomputable section

def original (x : ℝ) : ℝ := (Real.cos x - Real.cos (3 * x)) / x ^ 2
def productForm (x : ℝ) : ℝ := 2 * Real.sin (2 * x) * Real.sin x / x ^ 2
def normalized (x : ℝ) : ℝ :=
  4 * (Real.sin x / x) ^ 2 * Real.cos x
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 477, gap 1. -/
theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero productForm L := by
  have hfun : original = productForm := by
    funext x
    have hcos2 : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hnum :
        Real.cos x - Real.cos (3 * x) =
          2 * Real.sin (2 * x) * Real.sin x := by
      rw [show (3 : ℝ) * x = 2 * x + x by ring, Real.cos_add,
        Real.sin_two_mul, hcos2]
      ring
    unfold original productForm
    rw [hnum]
  rw [hfun]

/-- Exercise 477, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero productForm L ↔ HasLimitAtZero normalized L := by
  have hfun : productForm = normalized := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [productForm, normalized]
    · unfold productForm normalized
      rw [Real.sin_two_mul]
      field_simp [hx]
      ring
  rw [hfun]

/-- Exercise 477, gap 3. -/
theorem gap3 : HasLimitAtZero normalized 4 := by
  unfold HasLimitAtZero
  have hsin :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin (0 : ℝ)).tendsto_slope_zero
  have hcos :
      Filter.Tendsto (fun x : ℝ => Real.cos x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hc :
        Filter.Tendsto Real.cos (nhds (0 : ℝ)) (nhds (Real.cos 0)) :=
      Real.continuous_cos.continuousAt
    rw [Real.cos_zero] at hc
    exact hc.mono_left inf_le_left
  have hconst :
      Filter.Tendsto (fun _ : ℝ => (4 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 4) :=
    tendsto_const_nhds
  change Filter.Tendsto
    (fun x : ℝ => 4 * (Real.sin x / x) ^ 2 * Real.cos x)
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 4)
  simpa using (hconst.mul (hsin.pow 2)).mul hcos

/-- Exercise 477, gap 4. -/
theorem gap4 : HasLimitAtZero original 4 := by
  exact (gap1 4).mpr ((gap2 4).mpr gap3)

end

end ProofGap.Exercise477
