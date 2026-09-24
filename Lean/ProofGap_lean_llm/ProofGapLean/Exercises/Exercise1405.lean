import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1405

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) := 1 / x - 1 / Real.sin x
def combined (x : ℝ) := (Real.sin x - x) / (x * Real.sin x)
def leadingStage (x : ℝ) := (-(1 / 6 : ℝ) * x) / (1 + x ^ 2)

private theorem base_limits :
    Tendsto original (punctured 0) (nhds 0) ∧
      Tendsto combined (punctured 0) (nhds 0) := by
  have sin_cubic_bound : ∀ x : ℝ, |Real.sin x - x| ≤ |x| ^ 3 := by
    have pos_bound : ∀ y : ℝ, 0 < y → |Real.sin y - y| ≤ y ^ 3 := by
      intro y hy
      have hf_diff : Differentiable ℝ (fun t : ℝ => Real.sin t - t) :=
        Real.differentiable_sin.sub differentiable_id
      obtain ⟨c, hc, hcslope⟩ :=
        exists_hasDerivAt_eq_slope
          (fun t : ℝ => Real.sin t - t)
          (fun t : ℝ => Real.cos t - 1) hy
          hf_diff.continuous.continuousOn
          (fun t _ => (Real.hasDerivAt_sin t).sub (hasDerivAt_id t))
      have hslope : (Real.sin y - y) / y = Real.cos c - 1 := by
        simpa [slope] using hcslope.symm
      have herr : Real.sin y - y = y * (Real.cos c - 1) := by
        simpa [mul_comm] using (div_eq_iff (ne_of_gt hy)).mp hslope
      have hg_diff : Differentiable ℝ (fun t : ℝ => Real.cos t - 1) :=
        Real.differentiable_cos.sub (differentiable_const 1)
      obtain ⟨d, hd, hdslope⟩ :=
        exists_hasDerivAt_eq_slope
          (fun t : ℝ => Real.cos t - 1)
          (fun t : ℝ => -Real.sin t) hc.1
          hg_diff.continuous.continuousOn
          (fun t _ => (Real.hasDerivAt_cos t).sub_const 1)
      have hslope' : (Real.cos c - 1) / c = -Real.sin d := by
        simpa [slope] using hdslope.symm
      have hcos : Real.cos c - 1 = c * (-Real.sin d) := by
        simpa [mul_comm] using (div_eq_iff (ne_of_gt hc.1)).mp hslope'
      have hsin : |Real.sin d| ≤ d := by
        simpa [abs_of_pos hd.1] using
          (Real.abs_sin_le_abs : |Real.sin d| ≤ |d|)
      have hmul₁ : y * c * |Real.sin d| ≤ y * c * d :=
        mul_le_mul_of_nonneg_left hsin
          (mul_nonneg (le_of_lt hy) (le_of_lt hc.1))
      have hdy : d ≤ y := le_trans (le_of_lt hd.2) (le_of_lt hc.2)
      have hcy : c ≤ y := le_of_lt hc.2
      have hcd : c * d ≤ y * y :=
        mul_le_mul hcy hdy (le_of_lt hd.1) (le_of_lt hy)
      have hmul₂ : y * (c * d) ≤ y * (y * y) :=
        mul_le_mul_of_nonneg_left hcd (le_of_lt hy)
      calc
        |Real.sin y - y| = y * c * |Real.sin d| := by
          rw [herr, hcos, abs_mul, abs_mul, abs_neg, abs_of_pos hy,
            abs_of_pos hc.1]
          ring
        _ ≤ y * c * d := hmul₁
        _ ≤ y * (y * y) := by simpa [mul_assoc] using hmul₂
        _ = y ^ 3 := by ring
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have h := pos_bound (-x) (neg_pos.mpr hx)
      calc
        |Real.sin x - x| = |Real.sin (-x) - (-x)| := by
          rw [show Real.sin (-x) - (-x) = -(Real.sin x - x) by
            rw [Real.sin_neg]
            ring, abs_neg]
        _ ≤ (-x) ^ 3 := h
        _ = |x| ^ 3 := by rw [abs_of_neg hx]
    · subst x
      norm_num
    · simpa [abs_of_pos hx] using pos_bound x hx
  have hid : Tendsto (fun x : ℝ => x) (punctured 0) (nhds 0) := by
    unfold punctured
    exact tendsto_id.mono_left inf_le_left
  have hne : ∀ᶠ x in punctured 0, x ≠ 0 := by
    unfold punctured
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have lower_sin : ∀ x : ℝ, |x| < 1 / 2 → |x| / 2 ≤ |Real.sin x| := by
    intro x hx
    have htri0 := abs_sub_le x (Real.sin x) 0
    rw [sub_zero, sub_zero, abs_sub_comm x (Real.sin x)] at htri0
    have hsquare : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      simpa [pow_two] using
        mul_self_le_mul_self (abs_nonneg x) (le_of_lt hx)
    have hcube : |x| ^ 3 ≤ |x| / 4 := by
      calc
        |x| ^ 3 = |x| * |x| ^ 2 := by ring
        _ ≤ |x| * ((1 / 2 : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsquare (abs_nonneg x)
        _ = |x| / 4 := by ring
    have htaylor := sin_cubic_bound x
    linarith [abs_nonneg x, abs_nonneg (Real.sin x)]
  have hsin_ne : ∀ᶠ x in punctured 0, Real.sin x ≠ 0 := by
    have hnear := Metric.tendsto_nhds.1 hid (1 / 2) (by norm_num)
    filter_upwards [hnear, hne] with x hxnear hxne
    have hxabs : |x| < 1 / 2 := by
      simpa [Real.dist_eq] using hxnear
    have hxpos : 0 < |x| := abs_pos.mpr hxne
    have hlower := lower_sin x hxabs
    have hhalf : 0 < |x| / 2 := div_pos hxpos (by norm_num)
    exact abs_pos.mp (lt_of_lt_of_le hhalf hlower)
  have hcomb : Tendsto combined (punctured 0) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hradius : 0 < min (1 / 2) (ε / 2) :=
      lt_min (by norm_num) (div_pos hε (by norm_num))
    have hnear := Metric.tendsto_nhds.1 hid (min (1 / 2) (ε / 2)) hradius
    filter_upwards [hnear, hne] with x hxnear hxne
    have hxabs : |x| < min (1 / 2) (ε / 2) := by
      simpa [Real.dist_eq] using hxnear
    have hxsmall : |x| < 1 / 2 :=
      lt_of_lt_of_le hxabs (min_le_left _ _)
    have hxeps : |x| < ε / 2 :=
      lt_of_lt_of_le hxabs (min_le_right _ _)
    have hxpos : 0 < |x| := abs_pos.mpr hxne
    have hlower := lower_sin x hxsmall
    have hsinpos : 0 < |Real.sin x| := by
      have hhalf : 0 < |x| / 2 := div_pos hxpos (by norm_num)
      exact lt_of_lt_of_le hhalf hlower
    have hdenpos : 0 < |x| * |Real.sin x| := mul_pos hxpos hsinpos
    have htaylor := sin_cubic_bound x
    have hscale : |x| * |x| ^ 2 < (ε / 2) * |x| ^ 2 :=
      mul_lt_mul_of_pos_right hxeps (pow_pos hxpos 2)
    have hnumlt : |x| ^ 3 < ε * (|x| ^ 2 / 2) := by
      nlinarith [hscale]
    have hscaleDen := mul_le_mul_of_nonneg_left hlower (abs_nonneg x)
    have hdenlower : |x| ^ 2 / 2 ≤ |x| * |Real.sin x| := by
      nlinarith [hscaleDen]
    have hscaledDen := mul_le_mul_of_nonneg_left hdenlower (le_of_lt hε)
    rw [Real.dist_eq, sub_zero, combined, abs_div, abs_mul]
    apply (div_lt_iff₀ hdenpos).2
    linarith
  have heq : original =ᶠ[punctured 0] combined := by
    filter_upwards [hne, hsin_ne] with x hx hsin
    dsimp [original, combined]
    field_simp [hx, hsin] <;> ring
  have horig : Tendsto original (punctured 0) (nhds 0) :=
    (tendsto_congr' heq).2 hcomb
  exact ⟨horig, hcomb⟩

theorem gap1 : Tendsto original (punctured 0) (nhds 0) := by
  exact base_limits.1
theorem gap2 : Tendsto combined (punctured 0) (nhds 0) := by
  exact base_limits.2
theorem gap3 : Tendsto leadingStage (punctured 0) (nhds 0) := by
  unfold leadingStage punctured
  have hconst :
      Tendsto (fun _ : ℝ => -(1 / 6 : ℝ)) (nhds 0) (nhds (-(1 / 6 : ℝ))) :=
    tendsto_const_nhds
  have hnum :
      Tendsto (fun x : ℝ => -(1 / 6 : ℝ) * x) (nhds 0) (nhds 0) := by
    simpa using hconst.mul tendsto_id
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1) :=
    tendsto_const_nhds
  have hden :
      Tendsto (fun x : ℝ => 1 + x ^ 2) (nhds 0) (nhds 1) := by
    simpa using hone.add (tendsto_id.pow 2)
  have hfull :
      Tendsto (fun x : ℝ => (-(1 / 6 : ℝ) * x) / (1 + x ^ 2))
        (nhds 0) (nhds 0) := by
    simpa using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  exact hfull.mono_left inf_le_left
theorem gap4 : Tendsto leadingStage (punctured 0) (nhds 0) := by
  exact gap3
theorem gap5 : Tendsto original (punctured 0) (nhds 0) := by
  exact gap1

end
end ProofGap.Exercise1405
