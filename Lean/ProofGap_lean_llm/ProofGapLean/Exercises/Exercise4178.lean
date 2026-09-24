import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace ProofGap.Exercise4178

noncomputable section

open MeasureTheory

def delta (a b c : ℝ) : ℝ :=
  a * c - b ^ 2

def phi (a b c d e f x y : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x * y + c * y ^ 2 +
    2 * d * x + 2 * e * y + f

def shiftedX (a b x y : ℝ) : ℝ :=
  x + b / a * y

def beta (a b c d e f : ℝ) : ℝ :=
  f - d ^ 2 / a -
    (a * e - b * d) ^ 2 / (a * delta a b c)

def discriminantTerm (a b c d e f : ℝ) : ℝ :=
  a * c * f - b ^ 2 * f - c * d ^ 2 -
    a * e ^ 2 + 2 * b * d * e

def uCoord (a b d x y : ℝ) : ℝ :=
  Real.sqrt (-a) * x +
    b * Real.sqrt (-a) / a * y +
    d * Real.sqrt (-a) / a

def vCoord (a b c d e y : ℝ) : ℝ :=
  Real.sqrt (-(delta a b c / a)) * y +
    Real.sqrt (-(delta a b c / a)) *
      (a * e - b * d) / delta a b c

def inverseJacobian (a b c : ℝ) : ℝ :=
  1 / Real.sqrt (delta a b c)

def originalIntegral (a b c d e f : ℝ) : ℝ :=
  ∫ y : ℝ, ∫ x : ℝ, Real.exp (phi a b c d e f x y)

def transformedIntegral (a b c d e f : ℝ) : ℝ :=
  ∫ v : ℝ, ∫ u : ℝ,
    Real.exp (-u ^ 2 - v ^ 2 + beta a b c d e f) *
      inverseJacobian a b c

def standardGaussianIntegral : ℝ :=
  ∫ v : ℝ, ∫ u : ℝ, Real.exp (-(u ^ 2 + v ^ 2))

private theorem completed_square
    (a b c d e f x y : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    phi a b c d e f x y =
      a * (shiftedX a b x y + d / a) ^ 2 +
        delta a b c / a *
          (y + (a * e - b * d) / delta a b c) ^ 2 +
        beta a b c d e f := by
  have hane : a ≠ 0 := ne_of_lt ha
  have hdne : delta a b c ≠ 0 := ne_of_gt hdelta
  unfold phi shiftedX beta delta at *
  field_simp [hane, hdne]
  ring

private theorem beta_eq_discriminant
    (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    beta a b c d e f =
      discriminantTerm a b c d e f / delta a b c := by
  have hane : a ≠ 0 := ne_of_lt ha
  have hdne : delta a b c ≠ 0 := ne_of_gt hdelta
  unfold beta discriminantTerm delta at *
  field_simp [hane, hdne]
  ring

private theorem coordinate_square
    (a b c d e f x y : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    phi a b c d e f x y =
      -(uCoord a b d x y) ^ 2 -
        (vCoord a b c d e y) ^ 2 +
        beta a b c d e f := by
  have hane : a ≠ 0 := ne_of_lt ha
  have hdne : delta a b c ≠ 0 := ne_of_gt hdelta
  have hna : 0 ≤ -a := by linarith
  have hratio : 0 < -(delta a b c / a) := by
    have : delta a b c / a < 0 := div_neg_of_pos_of_neg hdelta ha
    linarith
  have hsqa : Real.sqrt (-a) ^ 2 = -a :=
    Real.sq_sqrt hna
  have hsqratio :
      Real.sqrt (-(delta a b c / a)) ^ 2 =
        -(delta a b c / a) :=
    Real.sq_sqrt hratio.le
  have hu :
      uCoord a b d x y =
        Real.sqrt (-a) *
          (shiftedX a b x y + d / a) := by
    unfold uCoord shiftedX
    field_simp [hane]
  have hv :
      vCoord a b c d e y =
        Real.sqrt (-(delta a b c / a)) *
          (y + (a * e - b * d) / delta a b c) := by
    unfold vCoord
    field_simp [hdne]
  rw [completed_square a b c d e f x y ha hdelta, hu, hv]
  rw [mul_pow, mul_pow, hsqa, hsqratio]
  ring

private theorem gaussian_integral :
    (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
  simpa using (integral_gaussian (b := (1 : ℝ)))

private theorem affine_gaussian_integral
    (A C : ℝ) (hA : 0 < A) :
    (∫ x : ℝ, Real.exp (-(A * x + C) ^ 2)) =
      Real.sqrt Real.pi / A := by
  let g : ℝ → ℝ := fun t => Real.exp (-(A * t) ^ 2)
  have hshift :
      (∫ x : ℝ, g (x + C / A)) = ∫ x : ℝ, g x :=
    integral_add_right_eq_self g (C / A)
  have hfun :
      (fun x : ℝ => Real.exp (-(A * x + C) ^ 2)) =
        fun x => g (x + C / A) := by
    funext x
    unfold g
    congr 2
    have hAne : A ≠ 0 := ne_of_gt hA
    field_simp [hAne]
  rw [hfun, hshift]
  have hscale :=
    Measure.integral_comp_mul_left
      (fun t : ℝ => Real.exp (-t ^ 2)) A
  have hscale' :
      (∫ x : ℝ, Real.exp (-(A * x) ^ 2)) =
        A⁻¹ * Real.sqrt Real.pi := by
    simpa [abs_of_pos (inv_pos.mpr hA), gaussian_integral,
      smul_eq_mul] using hscale
  unfold g
  rw [hscale']
  field_simp [ne_of_gt hA]

private theorem standardGaussianIntegral_value :
    standardGaussianIntegral = Real.pi := by
  have hfactor (u v : ℝ) :
      Real.exp (-(u ^ 2 + v ^ 2)) =
        Real.exp (-u ^ 2) * Real.exp (-v ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold standardGaussianIntegral
  simp_rw [hfactor]
  have hinner (v : ℝ) :
      (∫ u : ℝ, Real.exp (-u ^ 2) * Real.exp (-v ^ 2)) =
        Real.sqrt Real.pi * Real.exp (-v ^ 2) := by
    rw [integral_mul_const, gaussian_integral]
  simp_rw [hinner]
  rw [integral_const_mul, gaussian_integral]
  simpa [pow_two] using Real.sq_sqrt (le_of_lt Real.pi_pos)

private theorem transformedIntegral_factor
    (a b c d e f : ℝ) :
    transformedIntegral a b c d e f =
      inverseJacobian a b c *
        Real.exp (beta a b c d e f) *
        standardGaussianIntegral := by
  let K : ℝ :=
    inverseJacobian a b c * Real.exp (beta a b c d e f)
  have hpoint (u v : ℝ) :
      Real.exp (-u ^ 2 - v ^ 2 + beta a b c d e f) *
          inverseJacobian a b c =
        K * Real.exp (-(u ^ 2 + v ^ 2)) := by
    unfold K
    rw [show -u ^ 2 - v ^ 2 + beta a b c d e f =
        beta a b c d e f + (-(u ^ 2 + v ^ 2)) by ring]
    rw [Real.exp_add]
    ring
  unfold transformedIntegral standardGaussianIntegral
  simp_rw [hpoint]
  calc
    (∫ v : ℝ, ∫ u : ℝ, K * Real.exp (-(u ^ 2 + v ^ 2))) =
        ∫ v : ℝ, K * (∫ u : ℝ,
          Real.exp (-(u ^ 2 + v ^ 2))) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [integral_const_mul]
    _ = K * (∫ v : ℝ, ∫ u : ℝ,
          Real.exp (-(u ^ 2 + v ^ 2))) := by
      rw [integral_const_mul]
    _ = inverseJacobian a b c *
          Real.exp (beta a b c d e f) *
          (∫ v : ℝ, ∫ u : ℝ,
            Real.exp (-(u ^ 2 + v ^ 2))) := by
      rfl

private theorem sqrt_product
    (a b c : ℝ) (ha : a < 0) (hdelta : 0 < delta a b c) :
    Real.sqrt (-a) * Real.sqrt (-(delta a b c / a)) =
      Real.sqrt (delta a b c) := by
  have hane : a ≠ 0 := ne_of_lt ha
  have hna : 0 ≤ -a := by linarith
  have hratio : 0 < -(delta a b c / a) := by
    have : delta a b c / a < 0 := div_neg_of_pos_of_neg hdelta ha
    linarith
  have hsqa : Real.sqrt (-a) ^ 2 = -a :=
    Real.sq_sqrt hna
  have hsqratio :
      Real.sqrt (-(delta a b c / a)) ^ 2 =
        -(delta a b c / a) :=
    Real.sq_sqrt hratio.le
  have hsqdelta :
      Real.sqrt (delta a b c) ^ 2 = delta a b c :=
    Real.sq_sqrt hdelta.le
  have hprodSq :
      (Real.sqrt (-a) *
          Real.sqrt (-(delta a b c / a))) ^ 2 =
        delta a b c := by
    rw [mul_pow, hsqa, hsqratio]
    field_simp [hane]
  have hprodNonneg :
      0 ≤ Real.sqrt (-a) *
        Real.sqrt (-(delta a b c / a)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsqrtNonneg : 0 ≤ Real.sqrt (delta a b c) :=
    Real.sqrt_nonneg _
  nlinarith

private theorem originalIntegral_factor
    (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    originalIntegral a b c d e f =
      inverseJacobian a b c *
        Real.exp (beta a b c d e f) *
        standardGaussianIntegral := by
  let A : ℝ := Real.sqrt (-a)
  let B : ℝ := Real.sqrt (-(delta a b c / a))
  let s : ℝ := (a * e - b * d) / delta a b c
  let C : ℝ → ℝ := fun y =>
    b * Real.sqrt (-a) / a * y +
      d * Real.sqrt (-a) / a
  have hA : 0 < A := by
    unfold A
    exact Real.sqrt_pos.2 (by linarith)
  have hratio : 0 < -(delta a b c / a) := by
    have : delta a b c / a < 0 := div_neg_of_pos_of_neg hdelta ha
    linarith
  have hB : 0 < B := by
    unfold B
    exact Real.sqrt_pos.2 hratio
  have hu (x y : ℝ) :
      uCoord a b d x y = A * x + C y := by
    dsimp [A, C]
    unfold uCoord
    ring
  have hv (y : ℝ) :
      vCoord a b c d e y = B * y + B * s := by
    dsimp [B, s]
    unfold vCoord
    ring
  have hinner (y : ℝ) :
      (∫ x : ℝ, Real.exp (phi a b c d e f x y)) =
        (Real.sqrt Real.pi / A) *
          Real.exp (-(vCoord a b c d e y) ^ 2 +
            beta a b c d e f) := by
    calc
      (∫ x : ℝ, Real.exp (phi a b c d e f x y)) =
          ∫ x : ℝ,
            Real.exp (-(uCoord a b d x y) ^ 2) *
              Real.exp (-(vCoord a b c d e y) ^ 2 +
                beta a b c d e f) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [coordinate_square a b c d e f x y ha hdelta]
        rw [show
            -(uCoord a b d x y) ^ 2 -
                (vCoord a b c d e y) ^ 2 +
                beta a b c d e f =
              -(uCoord a b d x y) ^ 2 +
                (-(vCoord a b c d e y) ^ 2 +
                  beta a b c d e f) by ring]
        rw [Real.exp_add]
      _ = (∫ x : ℝ,
            Real.exp (-(uCoord a b d x y) ^ 2)) *
            Real.exp (-(vCoord a b c d e y) ^ 2 +
              beta a b c d e f) := by
        rw [integral_mul_const]
      _ = (Real.sqrt Real.pi / A) *
            Real.exp (-(vCoord a b c d e y) ^ 2 +
              beta a b c d e f) := by
        rw [show
            (fun x : ℝ => Real.exp (-(uCoord a b d x y) ^ 2)) =
              fun x => Real.exp (-(A * x + C y) ^ 2) by
            funext x
            rw [hu]]
        rw [affine_gaussian_integral A (C y) hA]
  have houter :
      (∫ y : ℝ,
          Real.exp (-(vCoord a b c d e y) ^ 2 +
            beta a b c d e f)) =
        (Real.sqrt Real.pi / B) *
          Real.exp (beta a b c d e f) := by
    calc
      (∫ y : ℝ,
          Real.exp (-(vCoord a b c d e y) ^ 2 +
            beta a b c d e f)) =
          ∫ y : ℝ,
            Real.exp (-(vCoord a b c d e y) ^ 2) *
              Real.exp (beta a b c d e f) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.exp_add]
      _ = (∫ y : ℝ,
            Real.exp (-(vCoord a b c d e y) ^ 2)) *
            Real.exp (beta a b c d e f) := by
        rw [integral_mul_const]
      _ = (Real.sqrt Real.pi / B) *
            Real.exp (beta a b c d e f) := by
        rw [show
            (fun y : ℝ =>
              Real.exp (-(vCoord a b c d e y) ^ 2)) =
              fun y => Real.exp (-(B * y + B * s) ^ 2) by
            funext y
            rw [hv]]
        rw [affine_gaussian_integral B (B * s) hB]
  unfold originalIntegral
  simp_rw [hinner]
  rw [integral_const_mul, houter]
  rw [standardGaussianIntegral_value]
  unfold inverseJacobian
  have hAB :
      A * B = Real.sqrt (delta a b c) := by
    exact sqrt_product a b c ha hdelta
  have hAne : A ≠ 0 := ne_of_gt hA
  have hBne : B ≠ 0 := ne_of_gt hB
  have hsqrtne : Real.sqrt (delta a b c) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdelta)
  have hpisq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    nlinarith [Real.sq_sqrt (le_of_lt Real.pi_pos)]
  rw [show
      (Real.sqrt Real.pi / A) *
          (Real.sqrt Real.pi / B *
            Real.exp (beta a b c d e f)) =
        (1 / Real.sqrt (delta a b c)) *
          Real.exp (beta a b c d e f) * Real.pi by
      field_simp [hAne, hBne, hsqrtne]
      rw [pow_two, hpisq, hAB]
      ring]

theorem gap1 (a b c d e f x y : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    phi a b c d e f x y =
      a * (shiftedX a b x y + d / a) ^ 2 +
        delta a b c / a *
          (y + (a * e - b * d) / delta a b c) ^ 2 +
        beta a b c d e f := by
  exact completed_square a b c d e f x y ha hdelta

theorem gap2 (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    beta a b c d e f =
      f - d ^ 2 / a -
        (a * e - b * d) ^ 2 / (a * delta a b c) := by
  rfl

theorem gap3 (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    f - d ^ 2 / a -
        (a * e - b * d) ^ 2 / (a * delta a b c) =
      discriminantTerm a b c d e f / delta a b c := by
  simpa only [beta] using beta_eq_discriminant a b c d e f ha hdelta

theorem gap4 (a b c d e f : ℝ) :
    discriminantTerm a b c d e f =
      a * c * f - b ^ 2 * f - c * d ^ 2 -
        a * e ^ 2 + 2 * b * d * e := by
  rfl

theorem gap5 (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    beta a b c d e f =
      discriminantTerm a b c d e f / delta a b c := by
  exact beta_eq_discriminant a b c d e f ha hdelta

theorem gap6 (a b c d e f x y : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    phi a b c d e f x y =
      -(uCoord a b d x y) ^ 2 -
        (vCoord a b c d e y) ^ 2 +
        beta a b c d e f := by
  exact coordinate_square a b c d e f x y ha hdelta

theorem gap7 (a b c : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    inverseJacobian a b c =
      1 / Real.sqrt (delta a b c) := by
  rfl

theorem gap8 (a b c : ℝ)
    (hdelta : 0 < delta a b c) :
    0 < 1 / Real.sqrt (delta a b c) := by
  exact one_div_pos.mpr (Real.sqrt_pos.2 hdelta)

theorem gap9 (a b c : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    0 < inverseJacobian a b c := by
  unfold inverseJacobian
  exact one_div_pos.mpr (Real.sqrt_pos.2 hdelta)

theorem gap10 (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    originalIntegral a b c d e f =
      transformedIntegral a b c d e f := by
  rw [originalIntegral_factor a b c d e f ha hdelta]
  rw [transformedIntegral_factor a b c d e f]

theorem gap11 (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    transformedIntegral a b c d e f =
      inverseJacobian a b c *
        Real.exp
          (discriminantTerm a b c d e f / delta a b c) *
        standardGaussianIntegral := by
  rw [transformedIntegral_factor]
  rw [beta_eq_discriminant a b c d e f ha hdelta]

theorem gap12 (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    originalIntegral a b c d e f =
      inverseJacobian a b c *
        Real.exp
          (discriminantTerm a b c d e f / delta a b c) *
        standardGaussianIntegral := by
  rw [originalIntegral_factor a b c d e f ha hdelta]
  rw [beta_eq_discriminant a b c d e f ha hdelta]

theorem gap13 (a b c d e f : ℝ)
    (ha : a < 0) (hdelta : 0 < delta a b c) :
    originalIntegral a b c d e f =
      Real.pi / Real.sqrt (delta a b c) *
        Real.exp
          (discriminantTerm a b c d e f / delta a b c) := by
  rw [originalIntegral_factor a b c d e f ha hdelta]
  rw [beta_eq_discriminant a b c d e f ha hdelta]
  rw [standardGaussianIntegral_value]
  unfold inverseJacobian
  ring

end

end ProofGap.Exercise4178
