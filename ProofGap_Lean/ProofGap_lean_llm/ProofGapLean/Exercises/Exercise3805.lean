import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3805

noncomputable section

open MeasureTheory

def weightedGaussian (a b c a₁ b₁ c₁ x : ℝ) : ℝ :=
  (a₁ * x ^ 2 + 2 * b₁ * x + c₁) *
    Real.exp (-(a * x ^ 2 + 2 * b * x + c))

private def transformedIntegrand
    (a b a₁ b₁ c₁ t : ℝ) : ℝ :=
  (a₁ / a * t ^ 2 +
      2 * (a * b₁ - a₁ * b) / (a * Real.sqrt a) * t +
      (a₁ * b ^ 2 - 2 * a * b * b₁) / a ^ 2 + c₁) *
    Real.exp (-(t ^ 2))

private lemma weightedGaussian_eq_transformed
    (a b c a₁ b₁ c₁ x : ℝ) (ha : 0 < a) :
    weightedGaussian a b c a₁ b₁ c₁ x =
      Real.exp ((b ^ 2 - a * c) / a) *
        transformedIntegrand a b a₁ b₁ c₁
          ((a * x + b) / Real.sqrt a) := by
  have hspos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsne : Real.sqrt a ≠ 0 := hspos.ne'
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hpoly :
      a₁ * x ^ 2 + 2 * b₁ * x + c₁ =
        a₁ / a * ((a * x + b) / Real.sqrt a) ^ 2 +
          2 * (a * b₁ - a₁ * b) / (a * Real.sqrt a) *
            ((a * x + b) / Real.sqrt a) +
          (a₁ * b ^ 2 - 2 * a * b * b₁) / a ^ 2 + c₁ := by
    field_simp [ha.ne', hsne]
    rw [hsq]
    ring
  have hexponent :
      -(a * x ^ 2 + 2 * b * x + c) =
        (b ^ 2 - a * c) / a -
          ((a * x + b) / Real.sqrt a) ^ 2 := by
    field_simp [ha.ne', hsne]
    rw [hsq]
    ring
  unfold weightedGaussian transformedIntegrand
  rw [hpoly, hexponent, Real.exp_sub, Real.exp_neg]
  ring

theorem gap1 (a b c x t : ℝ) (ha : 0 < a)
    (hdisc : 0 < a * c - b ^ 2)
    (ht : t = (a * x + b) / Real.sqrt a) :
    x = (Real.sqrt a * t - b) / a := by
  have hsne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  rw [ht]
  field_simp [ha.ne', hsne]
  ring

theorem gap2 (a b c a₁ b₁ c₁ : ℝ) (ha : 0 < a)
    (hdisc : 0 < a * c - b ^ 2) :
    (∫ x : ℝ, weightedGaussian a b c a₁ b₁ c₁ x) =
      1 / Real.sqrt a * Real.exp ((b ^ 2 - a * c) / a) *
        ∫ t : ℝ,
          (a₁ / a * t ^ 2 +
            2 * (a * b₁ - a₁ * b) / (a * Real.sqrt a) * t +
            (a₁ * b ^ 2 - 2 * a * b * b₁) / a ^ 2 + c₁) *
              Real.exp (-(t ^ 2)) := by
  change
    (∫ x : ℝ, weightedGaussian a b c a₁ b₁ c₁ x) =
      1 / Real.sqrt a * Real.exp ((b ^ 2 - a * c) / a) *
        ∫ t : ℝ, transformedIntegrand a b a₁ b₁ c₁ t
  have hspos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsne : Real.sqrt a ≠ 0 := hspos.ne'
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have htform (x : ℝ) :
      (a * x + b) / Real.sqrt a =
        Real.sqrt a * x + b / Real.sqrt a := by
    field_simp [hsne]
    rw [hsq]
    nlinarith
  have haffine :
      (∫ x : ℝ,
          transformedIntegrand a b a₁ b₁ c₁
            ((a * x + b) / Real.sqrt a)) =
        1 / Real.sqrt a *
          ∫ t : ℝ, transformedIntegrand a b a₁ b₁ c₁ t := by
    calc
      (∫ x : ℝ,
          transformedIntegrand a b a₁ b₁ c₁
            ((a * x + b) / Real.sqrt a)) =
          ∫ x : ℝ,
            transformedIntegrand a b a₁ b₁ c₁
              (Real.sqrt a * x + b / Real.sqrt a) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [htform]
      _ = |(Real.sqrt a)⁻¹| •
          ∫ y : ℝ,
            transformedIntegrand a b a₁ b₁ c₁
              (y + b / Real.sqrt a) :=
        Measure.integral_comp_mul_left
          (fun y : ℝ =>
            transformedIntegrand a b a₁ b₁ c₁
              (y + b / Real.sqrt a))
          (Real.sqrt a)
      _ = |(Real.sqrt a)⁻¹| •
          ∫ y : ℝ, transformedIntegrand a b a₁ b₁ c₁ y := by
        rw [integral_add_right_eq_self]
      _ = 1 / Real.sqrt a *
          ∫ y : ℝ, transformedIntegrand a b a₁ b₁ c₁ y := by
        rw [abs_of_pos (inv_pos.2 hspos)]
        simp only [one_div, smul_eq_mul]
  calc
    (∫ x : ℝ, weightedGaussian a b c a₁ b₁ c₁ x) =
        ∫ x : ℝ,
          Real.exp ((b ^ 2 - a * c) / a) *
            transformedIntegrand a b a₁ b₁ c₁
              ((a * x + b) / Real.sqrt a) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact weightedGaussian_eq_transformed
        a b c a₁ b₁ c₁ x ha
    _ = Real.exp ((b ^ 2 - a * c) / a) *
        ∫ x : ℝ,
          transformedIntegrand a b a₁ b₁ c₁
            ((a * x + b) / Real.sqrt a) := by
      rw [MeasureTheory.integral_const_mul]
    _ = 1 / Real.sqrt a * Real.exp ((b ^ 2 - a * c) / a) *
        ∫ t : ℝ, transformedIntegrand a b a₁ b₁ c₁ t := by
      rw [haffine]
      ring

theorem gap3 :
    (∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2))) =
      Real.sqrt Real.pi / 2 := by
  have hgauss :
      Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [one_mul, neg_mul] using
      (integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos)
  have hmoment :
      Integrable (fun t : ℝ => t ^ 2 * Real.exp (-(t ^ 2))) := by
    simpa [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq
        (b := (1 : ℝ)) one_pos (s := (2 : ℝ)) (by norm_num))
  let F : ℝ → ℝ := fun t => t * Real.exp (-(t ^ 2))
  let F' : ℝ → ℝ :=
    fun t => Real.exp (-(t ^ 2)) -
      2 * (t ^ 2 * Real.exp (-(t ^ 2)))
  have hF : Integrable F := by
    dsimp [F]
    simpa only [one_mul, neg_mul] using
      (integrable_mul_exp_neg_mul_sq (b := (1 : ℝ)) one_pos)
  have hF' : Integrable F' := by
    exact hgauss.sub (hmoment.const_mul 2)
  have hderiv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    have hexp :
        HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2)))
          (-2 * t * Real.exp (-(t ^ 2))) t := by
      convert
        (Real.hasDerivAt_exp (-(t ^ 2))).comp t
          ((hasDerivAt_pow 2 t).neg) using 1 <;>
        ring
    dsimp [F, F']
    convert (hasDerivAt_id t).mul hexp using 1 <;>
      simp only [id_eq] <;>
      ring
  have hzero :
      (∫ t : ℝ, F' t) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable hderiv hF' hF
  dsimp [F'] at hzero
  have hgval :
      (∫ t : ℝ, Real.exp (-(t ^ 2))) = Real.sqrt Real.pi := by
    simpa using (integral_gaussian (1 : ℝ))
  rw [integral_sub hgauss (hmoment.const_mul 2),
    MeasureTheory.integral_const_mul, hgval] at hzero
  linarith

theorem gap4 :
    (∫ t : ℝ, t * Real.exp (-(t ^ 2))) = 0 := by
  have hgauss :
      Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [one_mul, neg_mul] using
      (integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos)
  have hlinear :
      Integrable (fun t : ℝ => t * Real.exp (-(t ^ 2))) := by
    simpa only [one_mul, neg_mul] using
      (integrable_mul_exp_neg_mul_sq (b := (1 : ℝ)) one_pos)
  let F : ℝ → ℝ :=
    fun t => -(1 / 2 : ℝ) * Real.exp (-(t ^ 2))
  have hF : Integrable F := hgauss.const_mul _
  have hderiv :
      ∀ t : ℝ, HasDerivAt F
        (t * Real.exp (-(t ^ 2))) t := by
    intro t
    have hexp :
        HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2)))
          (-2 * t * Real.exp (-(t ^ 2))) t := by
      convert
        (Real.hasDerivAt_exp (-(t ^ 2))).comp t
          ((hasDerivAt_pow 2 t).neg) using 1 <;>
        ring
    dsimp [F]
    convert hexp.const_mul (-(1 / 2 : ℝ)) using 1 <;>
      ring
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    hderiv hlinear hF

theorem gap5 :
    (∫ t : ℝ, Real.exp (-(t ^ 2))) = Real.sqrt Real.pi := by
  simpa using (integral_gaussian (1 : ℝ))

private lemma integral_transformed
    (a b a₁ b₁ c₁ : ℝ) :
    (∫ t : ℝ, transformedIntegrand a b a₁ b₁ c₁ t) =
      a₁ / a * (Real.sqrt Real.pi / 2) +
        ((a₁ * b ^ 2 - 2 * a * b * b₁) / a ^ 2 + c₁) *
          Real.sqrt Real.pi := by
  have hgauss :
      Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa only [one_mul, neg_mul] using
      (integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos)
  have hlinear :
      Integrable (fun t : ℝ => t * Real.exp (-(t ^ 2))) := by
    simpa only [one_mul, neg_mul] using
      (integrable_mul_exp_neg_mul_sq (b := (1 : ℝ)) one_pos)
  have hmoment :
      Integrable (fun t : ℝ => t ^ 2 * Real.exp (-(t ^ 2))) := by
    simpa [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq
        (b := (1 : ℝ)) one_pos (s := (2 : ℝ)) (by norm_num))
  let A : ℝ := a₁ / a
  let B : ℝ := 2 * (a * b₁ - a₁ * b) / (a * Real.sqrt a)
  let C : ℝ :=
    (a₁ * b ^ 2 - 2 * a * b * b₁) / a ^ 2 + c₁
  have hrewrite :
      (∫ t : ℝ, transformedIntegrand a b a₁ b₁ c₁ t) =
        A * (∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2))) +
          B * (∫ t : ℝ, t * Real.exp (-(t ^ 2))) +
          C * (∫ t : ℝ, Real.exp (-(t ^ 2))) := by
    calc
      (∫ t : ℝ, transformedIntegrand a b a₁ b₁ c₁ t) =
          ∫ t : ℝ,
            A * (t ^ 2 * Real.exp (-(t ^ 2))) +
              B * (t * Real.exp (-(t ^ 2))) +
              C * Real.exp (-(t ^ 2)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        dsimp [A, B, C, transformedIntegrand]
        ring
      _ = (∫ t : ℝ,
            A * (t ^ 2 * Real.exp (-(t ^ 2))) +
              B * (t * Real.exp (-(t ^ 2)))) +
          ∫ t : ℝ, C * Real.exp (-(t ^ 2)) := by
        simpa only [Pi.add_apply] using
          integral_add
            ((hmoment.const_mul A).add (hlinear.const_mul B))
            (hgauss.const_mul C)
      _ = A * (∫ t : ℝ, t ^ 2 * Real.exp (-(t ^ 2))) +
          B * (∫ t : ℝ, t * Real.exp (-(t ^ 2))) +
          C * (∫ t : ℝ, Real.exp (-(t ^ 2))) := by
        rw [show (∫ t : ℝ,
              A * (t ^ 2 * Real.exp (-(t ^ 2))) +
                B * (t * Real.exp (-(t ^ 2)))) =
            (∫ t : ℝ, A * (t ^ 2 * Real.exp (-(t ^ 2)))) +
              ∫ t : ℝ, B * (t * Real.exp (-(t ^ 2))) by
            simpa only [Pi.add_apply] using
              integral_add (hmoment.const_mul A) (hlinear.const_mul B),
          integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hrewrite, gap3, gap4, gap5]
  dsimp [A, B, C]
  ring

theorem gap6 (a b c a₁ b₁ c₁ : ℝ) (ha : 0 < a)
    (hdisc : 0 < a * c - b ^ 2) :
    (∫ x : ℝ, weightedGaussian a b c a₁ b₁ c₁ x) =
      1 / Real.sqrt a * Real.exp ((b ^ 2 - a * c) / a) *
        (a₁ / a * (Real.sqrt Real.pi / 2) +
          ((a₁ * b ^ 2 - 2 * a * b * b₁) / a ^ 2 + c₁) *
            Real.sqrt Real.pi) := by
  rw [gap2 a b c a₁ b₁ c₁ ha hdisc]
  change
    1 / Real.sqrt a * Real.exp ((b ^ 2 - a * c) / a) *
        (∫ t : ℝ, transformedIntegrand a b a₁ b₁ c₁ t) =
      1 / Real.sqrt a * Real.exp ((b ^ 2 - a * c) / a) *
        (a₁ / a * (Real.sqrt Real.pi / 2) +
          ((a₁ * b ^ 2 - 2 * a * b * b₁) / a ^ 2 + c₁) *
            Real.sqrt Real.pi)
  rw [integral_transformed]

theorem gap7 (a b c a₁ b₁ c₁ : ℝ) (ha : 0 < a)
    (hdisc : 0 < a * c - b ^ 2) :
    (∫ x : ℝ, weightedGaussian a b c a₁ b₁ c₁ x) =
      ((a + 2 * b ^ 2) * a₁ - 4 * a * b * b₁ + 2 * a ^ 2 * c₁) /
          (2 * a ^ 2) *
        Real.sqrt (Real.pi / a) *
        Real.exp ((b ^ 2 - a * c) / a) := by
  rw [gap6 a b c a₁ b₁ c₁ ha hdisc]
  rw [Real.sqrt_div Real.pi_pos.le]
  have hsne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  field_simp [ha.ne', hsne]
  ring

end

end ProofGap.Exercise3805
