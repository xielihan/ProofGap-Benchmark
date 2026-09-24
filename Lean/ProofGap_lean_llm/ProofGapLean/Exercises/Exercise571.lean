import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise571

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.sqrt (1 + x * Real.sin x) - 1) / (Real.exp (x ^ 2) - 1)
def rationalized (x : ℝ) : ℝ :=
  (x * Real.sin x) /
    ((Real.exp (x ^ 2) - 1) * (Real.sqrt (1 + x * Real.sin x) + 1))
def normalized (x : ℝ) : ℝ :=
  (Real.sin x / x) /
    (((Real.exp (x ^ 2) - 1) / x ^ 2) *
      (1 + Real.sqrt (1 + x * Real.sin x)))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 571, gap 1. -/
private lemma exp_sq_sub_one_ne_zero {x : ℝ} (hx : x ≠ 0) :
    Real.exp (x ^ 2) - 1 ≠ 0 := by
  have hx2 : 0 < x ^ 2 := by
    simpa [pow_two] using (mul_self_pos.mpr hx)
  exact ne_of_gt (sub_pos.mpr ((Real.one_lt_exp_iff).2 hx2))

private lemma sqrt_add_one_ne_zero (y : ℝ) :
    Real.sqrt y + 1 ≠ 0 := by
  exact ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg y) zero_lt_one)

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rationalized L := by
  unfold HasLimitAtZero
  have harg :
      Filter.Tendsto (fun x : ℝ => 1 + x * Real.sin x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hc : Continuous (fun x : ℝ => 1 + x * Real.sin x) :=
      continuous_const.add (continuous_id.mul Real.continuous_sin)
    have harg0 :
        Filter.Tendsto (fun x : ℝ => 1 + x * Real.sin x)
          (nhds (0 : ℝ)) (nhds (1 + (0 : ℝ) * Real.sin 0)) :=
      hc.continuousAt
    simpa using harg0.mono_left inf_le_left
  have hpos :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        0 < 1 + x * Real.sin x :=
    harg.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  apply Filter.tendsto_congr'
  filter_upwards [self_mem_nhdsWithin, hpos] with x hx hxpos
  have hx0 : x ≠ 0 := by
    simpa using hx
  have hD : Real.exp (x ^ 2) - 1 ≠ 0 :=
    exp_sq_sub_one_ne_zero hx0
  have hs : Real.sqrt (1 + x * Real.sin x) + 1 ≠ 0 :=
    sqrt_add_one_ne_zero _
  unfold original rationalized
  field_simp [hD, hs]
  nlinarith [Real.sq_sqrt (le_of_lt hxpos)]

/-- Exercise 571, gap 2. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero rationalized L ↔ HasLimitAtZero normalized L := by
  unfold HasLimitAtZero
  apply Filter.tendsto_congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by
    simpa using hx
  have hD : Real.exp (x ^ 2) - 1 ≠ 0 :=
    exp_sq_sub_one_ne_zero hx0
  have hs : Real.sqrt (1 + x * Real.sin x) + 1 ≠ 0 :=
    sqrt_add_one_ne_zero _
  have hs' : 1 + Real.sqrt (1 + x * Real.sin x) ≠ 0 := by
    simpa [add_comm] using hs
  unfold rationalized normalized
  field_simp [hx0, hD, hs, hs'] <;> ring

/-- Exercise 571, gap 3. -/
theorem gap3 : HasLimitAtZero normalized (1 / 2) := by
  unfold HasLimitAtZero
  have hsq :
      Filter.Tendsto (fun x : ℝ => x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc_id : Continuous (fun x : ℝ => x) := continuous_id
      have hfull :
          Filter.Tendsto (fun x : ℝ => x ^ 2)
            (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ 2)) :=
        (hc_id.pow 2).continuousAt
      simpa using hfull.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by
        simpa using hx
      simpa [hx0]
  have hexp0 :
      Filter.Tendsto (fun y : ℝ => (Real.exp y - 1) / y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h := (((hasDerivAt_id (0 : ℝ)).exp).tendsto_slope)
    have heq :
        (fun y : ℝ => (Real.exp y - 1) / y) =
          slope (fun y : ℝ => Real.exp y) 0 := by
      funext y
      change (Real.exp y - 1) / y =
        (y - 0)⁻¹ • (Real.exp y - Real.exp 0)
      simp only [sub_zero, Real.exp_zero, smul_eq_mul, div_eq_mul_inv]
      rw [mul_comm]
    rw [heq]
    simpa using h
  have hexp :
      Filter.Tendsto (fun x : ℝ => (Real.exp (x ^ 2) - 1) / x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hexp0.comp hsq
  have hsin :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h := (((hasDerivAt_id (0 : ℝ)).sin).tendsto_slope)
    have heq :
        (fun x : ℝ => Real.sin x / x) =
          slope (fun x : ℝ => Real.sin x) 0 := by
      funext x
      change Real.sin x / x =
        (x - 0)⁻¹ • (Real.sin x - Real.sin 0)
      simp only [sub_zero, Real.sin_zero, smul_eq_mul, div_eq_mul_inv]
      rw [mul_comm]
    rw [heq]
    simpa using h
  have hsqrt :
      Filter.Tendsto
        (fun x : ℝ => 1 + Real.sqrt (1 + x * Real.sin x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    have hc : Continuous
        (fun x : ℝ => 1 + Real.sqrt (1 + x * Real.sin x)) :=
      continuous_const.add
        (Real.continuous_sqrt.comp
          (continuous_const.add (continuous_id.mul Real.continuous_sin)))
    have hfull :
        Filter.Tendsto
          (fun x : ℝ => 1 + Real.sqrt (1 + x * Real.sin x))
          (nhds (0 : ℝ))
          (nhds (1 + Real.sqrt (1 + (0 : ℝ) * Real.sin 0))) :=
      hc.continuousAt
    have hsource :
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ ≤ nhds (0 : ℝ) :=
      inf_le_left
    norm_num at hfull
    exact hfull.mono_left hsource
  have hden := hexp.mul hsqrt
  have hquot := hsin.div hden (by norm_num : (1 : ℝ) * 2 ≠ 0)
  simpa [normalized] using hquot

/-- Exercise 571, gap 4. -/
theorem gap4 : HasLimitAtZero original (1 / 2) := by
  exact
    (gap1 (1 / 2 : ℝ)).mpr
      ((gap2 (1 / 2 : ℝ)).mpr gap3)

end

end ProofGap.Exercise571
