import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise517

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (x : ℝ) : ℝ := Real.rpow (1 + x ^ 2) (cot x ^ 2)
def transformed (x : ℝ) : ℝ :=
  Real.rpow (1 + x ^ 2) (1 / x ^ 2) *
    (x / Real.sin x) ^ 2 * Real.cos x ^ 2
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 517, gap 1; interpret variable powers by `Real.rpow`. -/
private theorem square_punctured_tendsto :
    Filter.Tendsto (fun x : ℝ => x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  change
    Filter.map (fun x : ℝ => x ^ 2) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) ≤
      nhds 0 ⊓ Filter.principal (({0} : Set ℝ)ᶜ)
  refine le_inf ?_ ?_
  · simpa using
      (((continuous_id : Continuous fun x : ℝ => x).pow 2).tendsto 0).mono_left
        (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  · apply Filter.tendsto_principal.2
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simpa using pow_ne_zero 2 hx0

private theorem log_one_plus_div_tendsto :
    Filter.Tendsto
      (fun u : ℝ => Real.log (1 + u) / u)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    ((Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 from one_ne_zero)).tendsto_slope_zero)

private theorem log_ratio_tendsto :
    Filter.Tendsto
      (fun x : ℝ => Real.log (1 + x ^ 2) / x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa only [Function.comp_apply] using
    (log_one_plus_div_tendsto.comp square_punctured_tendsto)

private theorem sin_div_tendsto :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    ((Real.hasDerivAt_sin 0).tendsto_slope_zero)

private theorem x_div_sin_tendsto :
    Filter.Tendsto (fun x : ℝ => x / Real.sin x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have h :
      Filter.Tendsto (fun x : ℝ => (1 : ℝ) / (Real.sin x / x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((1 : ℝ) / 1)) :=
    tendsto_const_nhds.div sin_div_tendsto one_ne_zero
  have h' :
      Filter.Tendsto (fun x : ℝ => (1 : ℝ) / (Real.sin x / x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  field_simp [hx0]

private theorem cos_punctured_tendsto :
    Filter.Tendsto Real.cos
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa using
    (Real.continuous_cos.tendsto 0).mono_left
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)

private theorem transformed_limit :
    HasLimitAtZero transformed (Real.exp 1) := by
  have hbase :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow (1 + x ^ 2) (1 / x ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1)) := by
    have hexp :
        Filter.Tendsto
          (fun x : ℝ => Real.exp (Real.log (1 + x ^ 2) / x ^ 2))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1)) := by
      simpa only [Function.comp_apply] using
        (Real.continuous_exp.tendsto 1).comp log_ratio_tendsto
    refine hexp.congr' (Filter.Eventually.of_forall ?_)
    intro x
    have hpos : 0 < 1 + x ^ 2 := by positivity
    have hrpow :
        Real.rpow (1 + x ^ 2) (1 / x ^ 2) =
          Real.exp (Real.log (1 + x ^ 2) * (1 / x ^ 2)) := by
      exact Real.rpow_def_of_pos (y := (1 / x ^ 2 : ℝ)) hpos
    symm
    calc
      Real.rpow (1 + x ^ 2) (1 / x ^ 2) =
          Real.exp (Real.log (1 + x ^ 2) * (1 / x ^ 2)) := hrpow
      _ = Real.exp (Real.log (1 + x ^ 2) / x ^ 2) := by
        congr 1
        ring
  have hsin2 :
      Filter.Tendsto (fun x : ℝ => (x / Real.sin x) ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [one_pow] using x_div_sin_tendsto.pow 2
  have hcos2 :
      Filter.Tendsto (fun x : ℝ => Real.cos x ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [one_pow] using cos_punctured_tendsto.pow 2
  change
    Filter.Tendsto
      (fun x : ℝ =>
        Real.rpow (1 + x ^ 2) (1 / x ^ 2) *
          (x / Real.sin x) ^ 2 * Real.cos x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1))
  simpa only [mul_one] using (hbase.mul hsin2).mul hcos2

private theorem original_limit :
    HasLimitAtZero original (Real.exp 1) := by
  have hxcot :
      Filter.Tendsto (fun x : ℝ => x * cot x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h :
        Filter.Tendsto (fun x : ℝ => x / Real.sin x * Real.cos x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      simpa only [one_mul] using
        x_div_sin_tendsto.mul cos_punctured_tendsto
    refine h.congr' (Filter.Eventually.of_forall ?_)
    intro x
    simp only [cot, div_eq_mul_inv]
    ring
  have hproduct :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log (1 + x ^ 2) / x ^ 2 * (x * cot x) ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [one_pow, mul_one] using
      log_ratio_tendsto.mul (hxcot.pow 2)
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (Real.log (1 + x ^ 2) / x ^ 2 * (x * cot x) ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_exp.tendsto 1).comp hproduct
  change Filter.Tendsto original
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1))
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  unfold original
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hrpow :
      Real.rpow (1 + x ^ 2) (cot x ^ 2) =
        Real.exp (Real.log (1 + x ^ 2) * (cot x ^ 2)) := by
    exact Real.rpow_def_of_pos (y := (cot x ^ 2 : ℝ)) hpos
  symm
  calc
    Real.rpow (1 + x ^ 2) (cot x ^ 2) =
        Real.exp (Real.log (1 + x ^ 2) * (cot x ^ 2)) := hrpow
    _ = Real.exp
          (Real.log (1 + x ^ 2) / x ^ 2 * (x * cot x) ^ 2) := by
      congr 1
      field_simp [hx0]
      <;> ring

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero transformed L := by
  constructor
  · intro h
    have hL : L = Real.exp 1 :=
      tendsto_nhds_unique h original_limit
    rw [hL]
    exact transformed_limit
  · intro h
    have hL : L = Real.exp 1 :=
      tendsto_nhds_unique h transformed_limit
    rw [hL]
    exact original_limit

/-- Exercise 517, gap 2. -/
theorem gap2 : HasLimitAtZero transformed (Real.exp 1) := by
  exact transformed_limit

/-- Exercise 517, gap 3. -/
theorem gap3 : HasLimitAtZero original (Real.exp 1) := by
  exact (gap1 (Real.exp 1)).2 gap2

end

end ProofGap.Exercise517
