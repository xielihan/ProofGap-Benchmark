import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2356_1
noncomputable section

open Filter
open scoped Interval

def f (x : ℝ) : ℝ := Real.sin x ^ 2 + Real.cos (x * Real.sqrt 2) ^ 2
def rewritten (x : ℝ) : ℝ :=
  (1 - Real.cos (2 * x)) / 2 +
    (1 + Real.cos (2 * x * Real.sqrt 2)) / 2
def primitive (x : ℝ) : ℝ :=
  x - (1 / 4 : ℝ) * Real.sin (2 * x) +
    1 / (4 * Real.sqrt 2) * Real.sin (2 * x * Real.sqrt 2)
def average (x : ℝ) : ℝ := (1 / x) * ∫ ξ in (0 : ℝ)..x, f ξ
def normalizedExpression (x : ℝ) : ℝ :=
  1 - Real.sin (2 * x) / (4 * x) +
    Real.sin (2 * x * Real.sqrt 2) / (4 * x * Real.sqrt 2)
def HasMean (L : ℝ) : Prop := Tendsto average atTop (nhds L)

theorem gap1 (x : ℝ) :
    (∫ ξ in (0 : ℝ)..x, f ξ) = ∫ ξ in (0 : ℝ)..x, rewritten ξ := by
  apply intervalIntegral.integral_congr
  intro ξ _
  unfold f rewritten
  rw [Real.sin_sq ξ]
  rw [Real.cos_sq ξ]
  rw [Real.cos_sq (ξ * Real.sqrt 2)]
  ring_nf

theorem gap2 (x : ℝ) :
    (∫ ξ in (0 : ℝ)..x, rewritten ξ) = primitive x := by
  have hspos : 0 < Real.sqrt 2 :=
    lt_trans (by norm_num) Real.one_lt_sqrt_two
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt hspos
  have hderiv (y : ℝ) : HasDerivAt primitive (rewritten y) y := by
    have hlin₁ : HasDerivAt (fun z : ℝ => 2 * z) 2 y := by
      simpa using
        (hasDerivAt_const y (2 : ℝ)).mul (hasDerivAt_id y)
    have hsin₁ :
        HasDerivAt (fun z : ℝ => Real.sin (2 * z))
          (2 * Real.cos (2 * y)) y := by
      convert (Real.hasDerivAt_sin (2 * y)).comp y hlin₁ using 1 <;> ring
    have hlin₂ :
        HasDerivAt (fun z : ℝ => 2 * z * Real.sqrt 2)
          (2 * Real.sqrt 2) y := by
      simpa using hlin₁.mul_const (Real.sqrt 2)
    have hsin₂ :
        HasDerivAt (fun z : ℝ => Real.sin (2 * z * Real.sqrt 2))
          ((2 * Real.sqrt 2) * Real.cos (2 * y * Real.sqrt 2)) y := by
      convert
        (Real.hasDerivAt_sin (2 * y * Real.sqrt 2)).comp y hlin₂ using 1 <;>
        ring
    have hp :=
      ((hasDerivAt_id y).sub (hsin₁.const_mul (1 / 4 : ℝ))).add
        (hsin₂.const_mul (1 / (4 * Real.sqrt 2) : ℝ))
    convert hp using 1 <;>
      simp only [primitive, rewritten] <;>
      field_simp [hs] <;> ring
  have hcont : Continuous rewritten := by
    unfold rewritten
    continuity
  have hint : IntervalIntegrable rewritten MeasureTheory.volume (0 : ℝ) x :=
    hcont.intervalIntegrable _ _
  have hftc :
      (∫ ξ in (0 : ℝ)..x, rewritten ξ) = primitive x - primitive 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hderiv y) hint
  simpa [primitive] using hftc

theorem gap3 (x : ℝ) :
    (∫ ξ in (0 : ℝ)..x, f ξ) = primitive x := by
  rw [gap1, gap2]

theorem gap4 :
    HasMean 1 ↔ Tendsto average atTop (nhds 1) := by
  rfl

theorem gap5 :
    Tendsto average atTop (nhds 1) ↔
      Tendsto normalizedExpression atTop (nhds 1) := by
  have hspos : 0 < Real.sqrt 2 :=
    lt_trans (by norm_num) Real.one_lt_sqrt_two
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt hspos
  have heq : average =ᶠ[atTop] normalizedExpression := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold average normalizedExpression
    rw [gap3]
    unfold primitive
    field_simp [ne_of_gt hx, hs] <;> ring
  exact tendsto_congr' heq

theorem gap6 :
    Tendsto normalizedExpression atTop (nhds 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨1 / ε + 1, ?_⟩
  intro x hx
  have hinvε : 0 < 1 / ε := one_div_pos.mpr hε
  have hxpos : 0 < x := by nlinarith
  have hslt : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hspos : 0 < Real.sqrt 2 := by nlinarith
  have hd₁ : 0 < 4 * x := mul_pos (by norm_num) hxpos
  have hd₂ : 0 < 4 * x * Real.sqrt 2 := mul_pos hd₁ hspos
  have hsin₁ : |Real.sin (2 * x)| ≤ 1 := Real.abs_sin_le_one _
  have hsin₂ : |Real.sin (2 * x * Real.sqrt 2)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hb₁ :
      |Real.sin (2 * x) / (4 * x)| ≤ 1 / (4 * x) := by
    rw [abs_div, abs_of_pos hd₁]
    exact div_le_div_of_nonneg_right hsin₁ (le_of_lt hd₁)
  have hb₂ :
      |Real.sin (2 * x * Real.sqrt 2) / (4 * x * Real.sqrt 2)| ≤
        1 / (4 * x * Real.sqrt 2) := by
    rw [abs_div, abs_of_pos hd₂]
    exact div_le_div_of_nonneg_right hsin₂ (le_of_lt hd₂)
  have hxs : x ≤ x * Real.sqrt 2 := by
    calc
      x = x * 1 := by ring
      _ ≤ x * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left (le_of_lt hslt) (le_of_lt hxpos)
  have hinv :
      1 / (4 * x * Real.sqrt 2) ≤ 1 / (4 * x) := by
    apply (div_le_div_iff₀ hd₂ hd₁).2
    nlinarith
  have hsum :
      1 / (4 * x) + 1 / (4 * x * Real.sqrt 2) ≤ 1 / (2 * x) := by
    calc
      1 / (4 * x) + 1 / (4 * x * Real.sqrt 2) ≤
          1 / (4 * x) + 1 / (4 * x) :=
        add_le_add (le_refl (1 / (4 * x))) hinv
      _ = 1 / (2 * x) := by
        field_simp [ne_of_gt hxpos] <;> ring
  have heq : ε * (1 / ε) = 1 := by
    field_simp [ne_of_gt hε]
  have hmul := mul_le_mul_of_nonneg_left hx (le_of_lt hε)
  have hsmall : 1 / (2 * x) < ε := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hxpos)).2
    nlinarith
  have habs :
      |normalizedExpression x - 1| ≤
        |Real.sin (2 * x) / (4 * x)| +
          |Real.sin (2 * x * Real.sqrt 2) / (4 * x * Real.sqrt 2)| := by
    calc
      |normalizedExpression x - 1| =
          |-(Real.sin (2 * x) / (4 * x)) +
            Real.sin (2 * x * Real.sqrt 2) / (4 * x * Real.sqrt 2)| := by
              unfold normalizedExpression
              congr 1
              ring
      _ ≤ |-(Real.sin (2 * x) / (4 * x))| +
            |Real.sin (2 * x * Real.sqrt 2) / (4 * x * Real.sqrt 2)| :=
          abs_add_le _ _
      _ = |Real.sin (2 * x) / (4 * x)| +
            |Real.sin (2 * x * Real.sqrt 2) / (4 * x * Real.sqrt 2)| := by
          rw [abs_neg]
  rw [Real.dist_eq]
  exact lt_of_le_of_lt
    (habs.trans ((add_le_add hb₁ hb₂).trans hsum)) hsmall

theorem gap7 : HasMean 1 := by
  exact gap4.mpr (gap5.mpr gap6)

end
end ProofGap.Exercise2356_1
