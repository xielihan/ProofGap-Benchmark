import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Order.Filter.Prod

namespace ProofGap.Exercise3191

noncomputable section

open Filter
open scoped Topology

def originalPower (p : ℝ × ℝ) : ℝ :=
  Real.rpow (1 + 1 / p.1) (p.1 ^ 2 / (p.1 + p.2))

def exponentialForm (p : ℝ × ℝ) : ℝ :=
  Real.exp
    (p.1 * Real.log (1 + 1 / p.1) * (p.1 / (p.1 + p.2)))

-- Statement correction: the two-variable approach uses the product filter; coprod makes gap2 false.
def approachFilter (a : ℝ) : Filter (ℝ × ℝ) :=
  (atTop : Filter ℝ) ×ˢ (𝓝 a)

private theorem tendsto_first (a : ℝ) :
    Tendsto (fun p : ℝ × ℝ => p.1) (approachFilter a) atTop := by
  unfold approachFilter
  exact tendsto_fst

private theorem tendsto_second (a : ℝ) :
    Tendsto (fun p : ℝ × ℝ => p.2) (approachFilter a) (𝓝 a) := by
  unfold approachFilter
  exact tendsto_snd

private theorem tendsto_ratio (a : ℝ) :
    Tendsto (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))
      (approachFilter a) (𝓝 1) := by
  have hx := tendsto_first a
  have hy := tendsto_second a
  have hxinv :
      Tendsto (fun p : ℝ × ℝ => (p.1)⁻¹) (approachFilter a) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hx
  have hyx :
      Tendsto (fun p : ℝ × ℝ => p.2 * (p.1)⁻¹)
        (approachFilter a) (𝓝 0) := by
    simpa using hy.mul hxinv
  have hden :
      Tendsto (fun p : ℝ × ℝ => 1 + p.2 * (p.1)⁻¹)
        (approachFilter a) (𝓝 1) := by
    simpa using tendsto_const_nhds.add hyx
  have hinv :
      Tendsto (fun p : ℝ × ℝ => (1 + p.2 * (p.1)⁻¹)⁻¹)
        (approachFilter a) (𝓝 1) := by
    simpa using hden.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
  refine hinv.congr' ?_
  filter_upwards [hx.eventually (eventually_gt_atTop 0)] with p hp
  field_simp [ne_of_gt hp]

private theorem eventually_power_eq_exp (a : ℝ) :
    originalPower =ᶠ[approachFilter a] exponentialForm := by
  have hx := tendsto_first a
  filter_upwards [hx.eventually (eventually_gt_atTop 0)] with p hp
  have hbase : 0 < 1 + 1 / p.1 := by positivity
  rw [originalPower, exponentialForm]
  change (1 + 1 / p.1) ^ (p.1 ^ 2 / (p.1 + p.2) : ℝ) =
    Real.exp (p.1 * Real.log (1 + 1 / p.1) * (p.1 / (p.1 + p.2)))
  rw [Real.rpow_def_of_pos hbase]
  congr 1
  ring

theorem gap1 :
    ∀ a L : ℝ,
      Tendsto originalPower (approachFilter a) (𝓝 L) ↔
        Tendsto exponentialForm (approachFilter a) (𝓝 L) := by
  intro a L
  exact tendsto_congr' (eventually_power_eq_exp a)

theorem gap2 :
    ∀ a : ℝ,
      Tendsto exponentialForm (approachFilter a)
        (𝓝 (Real.exp (1 * 1))) := by
  intro a
  have hxlog :
      Tendsto (fun p : ℝ × ℝ =>
        p.1 * Real.log (1 + 1 / p.1))
        (approachFilter a) (𝓝 1) := by
    simpa using
      (Real.tendsto_mul_log_one_add_div_atTop 1).comp (tendsto_first a)
  have hproduct :
      Tendsto (fun p : ℝ × ℝ =>
        p.1 * Real.log (1 + 1 / p.1) * (p.1 / (p.1 + p.2)))
        (approachFilter a) (𝓝 (1 * 1)) :=
    hxlog.mul (tendsto_ratio a)
  simpa only [exponentialForm, Function.comp_apply, one_mul] using
    Real.continuous_exp.continuousAt.tendsto.comp hproduct

theorem gap3 : Real.exp (1 * 1) = Real.exp 1 := by
  norm_num

theorem gap4 :
    ∀ a : ℝ,
      Tendsto originalPower (approachFilter a) (𝓝 (Real.exp 1)) := by
  intro a
  rw [gap1 a (Real.exp 1)]
  simpa using gap2 a

end

end ProofGap.Exercise3191
