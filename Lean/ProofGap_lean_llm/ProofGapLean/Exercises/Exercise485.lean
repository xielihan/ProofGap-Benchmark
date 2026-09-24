import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise485

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (a x : ℝ) : ℝ := (cot x - cot a) / (x - a)
def transformed (a x : ℝ) : ℝ :=
  -(Real.sin (x - a) / (x - a)) / (Real.sin x * Real.sin a)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_485/1.txt`; remove the shadowed outer `x` and require `sin a≠0`. -/
private theorem original_limit_from_derivative (a : ℝ)
    (ha : Real.sin a ≠ 0) :
    HasLimitAt (original a) a (-1 / Real.sin a ^ 2) := by
  have hderiv : HasDerivAt cot (-1 / Real.sin a ^ 2) a := by
    unfold cot
    convert
      (Real.hasDerivAt_cos a).div (Real.hasDerivAt_sin a) ha using 1
    rw [← Real.sin_sq_add_cos_sq a]
    ring
  unfold HasLimitAt
  apply hderiv.tendsto_slope.congr'
  filter_upwards with x
  unfold slope original
  simp [div_eq_mul_inv, mul_comm]

theorem gap1 (a : ℝ) (ha : Real.sin a ≠ 0) (L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (transformed a) a L := by
  unfold HasLimitAt
  have hsin_nhds : ∀ᶠ x in nhds a, Real.sin x ≠ 0 :=
    Real.continuous_sin.continuousAt.eventually_ne ha
  have hsin :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, Real.sin x ≠ 0 :=
    (show nhdsWithin a ({a} : Set ℝ)ᶜ ≤ nhds a from inf_le_left) hsin_nhds
  have hne : ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, x ≠ a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have heq :
      original a =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] transformed a := by
    filter_upwards [hsin, hne] with x hx hxa
    unfold original transformed cot
    rw [Real.sin_sub]
    field_simp [ha, hx, sub_ne_zero.mpr hxa]
    all_goals ring
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_485/2.txt`; evaluate the varying factor inside the limit. -/
theorem gap2 (a : ℝ) (ha : Real.sin a ≠ 0) :
    HasLimitAt (transformed a) a (-1 / Real.sin a ^ 2) := by
  exact
    (gap1 a ha (-1 / Real.sin a ^ 2)).mp
      (original_limit_from_derivative a ha)

/-- Source: `proof_gap/exercise_485/3.txt`; require `sin a≠0`. -/
theorem gap3 (a : ℝ) (ha : Real.sin a ≠ 0) :
    HasLimitAt (original a) a (-1 / Real.sin a ^ 2) := by
  exact original_limit_from_derivative a ha

end

end ProofGap.Exercise485
