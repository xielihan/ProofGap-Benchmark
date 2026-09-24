import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace ProofGap.Exercise3830

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

private def dampedGaussian (b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-b * (x : ℂ) ^ 2)

private def tailCoefficient (b : ℂ) (x : ℝ) : ℂ :=
  -(1 / (2 * b)) * (x : ℂ)⁻¹

private theorem hasDerivAt_dampedGaussian (b : ℂ) (x : ℝ) :
    HasDerivAt (dampedGaussian b) ((-2 * b * x) * dampedGaussian b x) x := by
  unfold dampedGaussian
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt
  have hi : HasDerivAt (fun y : ℝ => -b * (y : ℂ) ^ 2) (-2 * b * x) x := by
    convert (hc.pow 2).const_mul (-b) using 1 <;> ring
  convert (Complex.hasDerivAt_exp _).comp x hi using 1
  ring

private theorem hasDerivAt_tailCoefficient
    {b : ℂ} (hb : b ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (tailCoefficient b) ((1 / (2 * b)) * (x : ℂ)⁻¹ ^ 2) x := by
  unfold tailCoefficient
  have hcx : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hinv : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹) (-((x : ℂ) ^ 2)⁻¹) x :=
    (hasDerivAt_inv hcx).comp_ofReal
  convert hinv.const_mul (-(1 / (2 * b))) using 1
  field_simp [hb]

private theorem intervalIntegral_dampedGaussian_tail
    {b : ℂ} (hb : b ≠ 0) {R B : ℝ} (hR : 0 < R) (hRB : R ≤ B) :
    (∫ x in R..B, dampedGaussian b x) =
      tailCoefficient b B * dampedGaussian b B -
        tailCoefficient b R * dampedGaussian b R -
        ∫ x in R..B,
          ((1 / (2 * b)) * (x : ℂ)⁻¹ ^ 2) * dampedGaussian b x := by
  let u' : ℝ → ℂ := fun x => (1 / (2 * b)) * (x : ℂ)⁻¹ ^ 2
  let v' : ℝ → ℂ := fun x => (-2 * b * x) * dampedGaussian b x
  have hnonzero : ∀ x ∈ [[R, B]], x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hRB] at hx
    exact (hR.trans_le hx.1).ne'
  have hu : ContinuousOn (tailCoefficient b) [[R, B]] := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    unfold tailCoefficient
    fun_prop (disch := aesop)
  have hv : ContinuousOn (dampedGaussian b) [[R, B]] := by
    unfold dampedGaussian
    fun_prop
  have hu' : IntervalIntegrable u' volume R B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    dsimp [u']
    fun_prop (disch := aesop)
  have hv' : IntervalIntegrable v' volume R B := by
    apply ContinuousOn.intervalIntegrable
    dsimp [v']
    fun_prop
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := tailCoefficient b) (v := dampedGaussian b) (u' := u') (v' := v')
      hu hv
      (fun x hx => hasDerivAt_tailCoefficient hb
        (hnonzero x (by
          rw [min_eq_left hRB, max_eq_right hRB] at hx
          rw [uIcc_of_le hRB]
          exact ⟨hx.1.le, hx.2.le⟩)))
      (fun x _ => hasDerivAt_dampedGaussian b x) hu' hv'
  have heq : (∫ x in R..B, dampedGaussian b x) =
      ∫ x in R..B, tailCoefficient b x * v' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxne := hnonzero x hx
    dsimp [tailCoefficient, v']
    field_simp [hb, hxne]
  rw [heq]
  dsimp [u'] at hparts
  exact hparts

private theorem norm_dampedGaussian_le_one
    {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖dampedGaussian b x‖ ≤ 1 := by
  rw [dampedGaussian, Complex.norm_exp]
  rw [Real.exp_le_one_iff]
  have hsquare : (x : ℂ) ^ 2 = ((x ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have hre : (-b * (x : ℂ) ^ 2).re = -b.re * x ^ 2 := by
    calc
      (-b * (x : ℂ) ^ 2).re =
          (-b * ((x ^ 2 : ℝ) : ℂ)).re :=
        congrArg Complex.re (congrArg (fun z : ℂ => -b * z) hsquare)
      _ = -b.re * x ^ 2 := by
        change (-b).re * x ^ 2 - (-b).im * 0 = -b.re * x ^ 2
        simp
  rw [hre]
  nlinarith [mul_nonneg hb (sq_nonneg x)]

private theorem norm_tailCoefficient_mul_le
    {b : ℂ} (hb : 1 ≤ ‖b‖) {x : ℝ} (hx : 0 < x) :
    ‖tailCoefficient b x‖ ≤ 1 / (2 * x) := by
  have hb0 : ‖b‖ ≠ 0 := by positivity
  rw [tailCoefficient, norm_mul, norm_neg, norm_div, norm_one, norm_mul]
  norm_num
  rw [abs_of_pos hx]
  have hbinv : ‖b‖⁻¹ ≤ 1 := (inv_le_one₀ (by positivity : 0 < ‖b‖)).2 hb
  calc
    ‖b‖⁻¹ * (1 / 2) * x⁻¹ ≤ 1 * (1 / 2) * x⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbinv (by norm_num)) (by positivity)
    _ = x⁻¹ * (1 / 2) := by ring

private theorem norm_remainder_integrand_le
    {b : ℂ} (hbre : 0 ≤ b.re) (hbnorm : 1 ≤ ‖b‖)
    {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * b)) * (x : ℂ)⁻¹ ^ 2) * dampedGaussian b x‖ ≤
      1 / (2 * x ^ 2) := by
  have hb0 : ‖b‖ ≠ 0 := by positivity
  rw [norm_mul, norm_mul, norm_div, norm_one, norm_mul]
  norm_num
  have hbinv : ‖b‖⁻¹ ≤ 1 := (inv_le_one₀ (by positivity : 0 < ‖b‖)).2 hbnorm
  have hcoef : 0 ≤ (x ^ 2)⁻¹ * (1 / 2 : ℝ) := by positivity
  have hdamp := norm_dampedGaussian_le_one hbre x
  have hprod : ‖b‖⁻¹ * ‖dampedGaussian b x‖ ≤ 1 := by
    calc
      ‖b‖⁻¹ * ‖dampedGaussian b x‖ ≤
          1 * ‖dampedGaussian b x‖ :=
        mul_le_mul_of_nonneg_right hbinv (norm_nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hdamp zero_le_one
      _ = 1 := one_mul 1
  calc
    ‖b‖⁻¹ * (1 / 2) * (x ^ 2)⁻¹ * ‖dampedGaussian b x‖ =
        ((x ^ 2)⁻¹ * (1 / 2)) *
          (‖b‖⁻¹ * ‖dampedGaussian b x‖) := by ring
    _ ≤ ((x ^ 2)⁻¹ * (1 / 2)) * 1 :=
      mul_le_mul_of_nonneg_left hprod hcoef
    _ = (x ^ 2)⁻¹ * (1 / 2) := mul_one _

private theorem intervalIntegral_one_div_two_mul_sq
    {R B : ℝ} (hR : 0 < R) (hRB : R ≤ B) :
    (∫ x in R..B, 1 / (2 * x ^ 2)) =
      1 / (2 * R) - 1 / (2 * B) := by
  have hB : 0 < B := hR.trans_le hRB
  calc
    (∫ x in R..B, 1 / (2 * x ^ 2)) =
        ∫ x in R..B, (1 / 2 : ℝ) * x ^ (-2 : ℤ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxpos : 0 < x := by
        rw [uIcc_of_le hRB] at hx
        exact hR.trans_le hx.1
      field_simp [hxpos.ne']
    _ = (1 / 2 : ℝ) * ∫ x in R..B, x ^ (-2 : ℤ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 1 / (2 * R) - 1 / (2 * B) := by
      rw [integral_zpow (n := (-2 : ℤ))]
      · norm_num
        field_simp [hR.ne', hB.ne']
        ring
      · right
        constructor
        · norm_num
        · rw [uIcc_of_le hRB]
          exact fun hx => (hR.trans_le hx.1).false

private theorem norm_intervalIntegral_dampedGaussian_tail_le
    {b : ℂ} (hb : b ≠ 0) (hbre : 0 ≤ b.re) (hbnorm : 1 ≤ ‖b‖)
    {R B : ℝ} (hR : 0 < R) (hRB : R ≤ B) :
    ‖∫ x in R..B, dampedGaussian b x‖ ≤ 1 / R := by
  have hB : 0 < B := hR.trans_le hRB
  have hidentity := intervalIntegral_dampedGaussian_tail hb hR hRB
  have hboundB :
      ‖tailCoefficient b B * dampedGaussian b B‖ ≤ 1 / (2 * B) := by
    rw [norm_mul]
    calc
      ‖tailCoefficient b B‖ * ‖dampedGaussian b B‖ ≤
          ‖tailCoefficient b B‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_dampedGaussian_le_one hbre B) (norm_nonneg _)
      _ ≤ (1 / (2 * B)) * 1 :=
        mul_le_mul_of_nonneg_right (norm_tailCoefficient_mul_le hbnorm hB) zero_le_one
      _ = 1 / (2 * B) := mul_one _
  have hboundR :
      ‖tailCoefficient b R * dampedGaussian b R‖ ≤ 1 / (2 * R) := by
    rw [norm_mul]
    calc
      ‖tailCoefficient b R‖ * ‖dampedGaussian b R‖ ≤
          ‖tailCoefficient b R‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_dampedGaussian_le_one hbre R) (norm_nonneg _)
      _ ≤ (1 / (2 * R)) * 1 :=
        mul_le_mul_of_nonneg_right (norm_tailCoefficient_mul_le hbnorm hR) zero_le_one
      _ = 1 / (2 * R) := mul_one _
  let q : ℝ → ℂ := fun x =>
    ((1 / (2 * b)) * (x : ℂ)⁻¹ ^ 2) * dampedGaussian b x
  let g : ℝ → ℝ := fun x => 1 / (2 * x ^ 2)
  have hgint : IntervalIntegrable g volume R B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    dsimp [g]
    have hxne : x ≠ 0 := by
      rw [uIcc_of_le hRB] at hx
      exact (hR.trans_le hx.1).ne'
    fun_prop (disch := aesop)
  have hqnorm :
      ‖∫ x in R..B, q x‖ ≤ ∫ x in R..B, g x := by
    apply intervalIntegral.norm_integral_le_of_norm_le hRB
    · exact Eventually.of_forall fun x _ =>
        norm_remainder_integrand_le hbre hbnorm
          (hR.trans ‹x ∈ Ioc R B›.1)
    · exact hgint
  rw [intervalIntegral_one_div_two_mul_sq hR hRB] at hqnorm
  rw [hidentity]
  calc
    ‖tailCoefficient b B * dampedGaussian b B -
        tailCoefficient b R * dampedGaussian b R -
        ∫ x in R..B, q x‖ ≤
      ‖tailCoefficient b B * dampedGaussian b B‖ +
        ‖tailCoefficient b R * dampedGaussian b R‖ +
        ‖∫ x in R..B, q x‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1 / (2 * B) + 1 / (2 * R) +
        (1 / (2 * R) - 1 / (2 * B)) := by gcongr
    _ = 1 / R := by field_simp [hR.ne', hB.ne']; ring

private def fresnelPartial (B : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..B, dampedGaussian (-Complex.I) x

private theorem norm_fresnelPartial_sub_le
    {R B C : ℝ} (hR : 0 < R) (hB : R ≤ B) (hC : R ≤ C) :
    ‖fresnelPartial B - fresnelPartial C‖ ≤ 1 / R := by
  have hcont : Continuous (dampedGaussian (-Complex.I)) := by
    unfold dampedGaussian
    fun_prop
  rcases le_total C B with hCB | hBC
  · have hdiff :
        fresnelPartial B - fresnelPartial C =
          ∫ x in C..B, dampedGaussian (-Complex.I) x := by
      exact intervalIntegral.integral_interval_sub_left
        (hcont.intervalIntegrable 0 B) (hcont.intervalIntegrable 0 C)
    rw [hdiff]
    exact (norm_intervalIntegral_dampedGaussian_tail_le
      (by simp) (by simp) (by simp) (hR.trans_le hC) hCB).trans
        (one_div_le_one_div_of_le hR hC)
  · have hdiff :
        fresnelPartial C - fresnelPartial B =
          ∫ x in B..C, dampedGaussian (-Complex.I) x := by
      exact intervalIntegral.integral_interval_sub_left
        (hcont.intervalIntegrable 0 C) (hcont.intervalIntegrable 0 B)
    rw [← norm_neg, neg_sub, hdiff]
    exact (norm_intervalIntegral_dampedGaussian_tail_le
      (by simp) (by simp) (by simp) (hR.trans_le hB) hBC).trans
        (one_div_le_one_div_of_le hR hB)

private theorem exists_tendsto_fresnelPartial :
    ∃ L : ℂ, Tendsto fresnelPartial atTop (𝓝 L) := by
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  constructor
  · infer_instance
  · intro ε hε
    let R : ℝ := 1 + 1 / ε
    have hR : 0 < R := by dsimp [R]; positivity
    have hbound : 1 / R < ε := by
      dsimp [R]
      calc
        1 / (1 + 1 / ε) = ε / (ε + 1) := by field_simp
        _ < ε := by
          rw [div_lt_iff₀ (by positivity : 0 < ε + 1)]
          nlinarith
    refine ⟨fresnelPartial '' Ici R, image_mem_map (Ici_mem_atTop R), ?_⟩
    intro z hz w hw
    rcases hz with ⟨B, hB, rfl⟩
    rcases hw with ⟨C, hC, rfl⟩
    rw [mem_Ici] at hB hC
    rw [dist_eq_norm]
    exact (norm_fresnelPartial_sub_le hR hB hC).trans_lt hbound

private def gaussianHalf (b : ℂ) : ℂ :=
  (Real.pi / b) ^ (1 / 2 : ℂ) / 2

private theorem norm_gaussianHalf_sub_partial_le
    {b : ℂ} (hbre : 0 < b.re) (hbnorm : 1 ≤ ‖b‖)
    {R : ℝ} (hR : 0 < R) :
    ‖gaussianHalf b - ∫ x in (0 : ℝ)..R, dampedGaussian b x‖ ≤ 1 / R := by
  have hlim :
      Tendsto (fun B : ℝ => ∫ x in (0 : ℝ)..B, dampedGaussian b x)
        atTop (𝓝 (gaussianHalf b)) := by
    have hi :=
      intervalIntegral_tendsto_integral_Ioi 0
        (integrable_cexp_neg_mul_sq hbre).integrableOn tendsto_id
    rw [integral_gaussian_complex_Ioi hbre] at hi
    simpa [dampedGaussian, gaussianHalf] using hi
  have hcont : Continuous (dampedGaussian b) := by
    unfold dampedGaussian
    fun_prop
  apply le_of_tendsto (hlim.sub tendsto_const_nhds).norm
  filter_upwards [eventually_ge_atTop R] with B hRB
  have hdiff :
      (∫ x in (0 : ℝ)..B, dampedGaussian b x) -
          ∫ x in (0 : ℝ)..R, dampedGaussian b x =
        ∫ x in R..B, dampedGaussian b x := by
    exact intervalIntegral.integral_interval_sub_left
      (hcont.intervalIntegrable 0 B) (hcont.intervalIntegrable 0 R)
  rw [hdiff]
  have hb : b ≠ 0 := by
    intro hb
    subst b
    simpa using hbre
  exact norm_intervalIntegral_dampedGaussian_tail_le hb hbre.le hbnorm hR hRB

private def abelCoefficient (B : ℝ) : ℂ :=
  ((1 / B ^ 4 : ℝ) : ℂ) - Complex.I

private theorem norm_abel_damped_sub_fresnel_le
    {B x : ℝ} (hB : 1 ≤ B) (hx : 0 ≤ x) (hxB : x ≤ B) :
    ‖dampedGaussian (abelCoefficient B) x -
        dampedGaussian (-Complex.I) x‖ ≤ 1 / B ^ 2 := by
  let a : ℝ := 1 / B ^ 4
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have heq :
      dampedGaussian (abelCoefficient B) x -
          dampedGaussian (-Complex.I) x =
        ((((Real.exp (-(a * x ^ 2)) : ℝ) : ℂ) - 1) *
          Complex.exp (Complex.I * (x : ℂ) ^ 2)) := by
    unfold dampedGaussian abelCoefficient
    dsimp [a]
    rw [show
      -(((1 / B ^ 4 : ℝ) : ℂ) - Complex.I) * (x : ℂ) ^ 2 =
        ((-(1 / B ^ 4 * x ^ 2) : ℝ) : ℂ) +
          Complex.I * (x : ℂ) ^ 2 by push_cast; ring]
    rw [Complex.exp_add, Complex.ofReal_exp]
    congr 1
    rw [show -(-Complex.I) * (x : ℂ) ^ 2 =
      Complex.I * (x : ℂ) ^ 2 by ring]
    ring
  rw [heq, norm_mul, Complex.norm_exp]
  have hcoe :
      (((Real.exp (-(a * x ^ 2)) : ℝ) : ℂ) - 1) =
        ((Real.exp (-(a * x ^ 2)) - 1 : ℝ) : ℂ) := by norm_num
  rw [hcoe, Complex.norm_real]
  have hre : (Complex.I * (x : ℂ) ^ 2).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub]
    rw [pow_two, Complex.mul_im]
    simp
  rw [hre, Real.exp_zero, mul_one]
  have hexple : Real.exp (-(a * x ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg ha (sq_nonneg x))
  have hexpnonneg : 0 ≤ Real.exp (-(a * x ^ 2)) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs]
  rw [abs_of_nonpos (by simpa using hexple), neg_sub]
  have hone : 1 - Real.exp (-(a * x ^ 2)) ≤ a * x ^ 2 := by
    linarith [Real.one_sub_le_exp_neg (a * x ^ 2)]
  calc
    1 - Real.exp (-(a * x ^ 2)) ≤ a * x ^ 2 := hone
    _ ≤ 1 / B ^ 2 := by
      dsimp [a]
      have hBpos : 0 < B := zero_lt_one.trans_le hB
      have hxsq : x ^ 2 ≤ B ^ 2 := by nlinarith
      calc
        1 / B ^ 4 * x ^ 2 ≤ 1 / B ^ 4 * B ^ 2 := by gcongr
        _ = 1 / B ^ 2 := by field_simp

private theorem norm_abel_partial_sub_fresnelPartial_le
    {B : ℝ} (hB : 1 ≤ B) :
    ‖(∫ x in (0 : ℝ)..B, dampedGaussian (abelCoefficient B) x) -
        fresnelPartial B‖ ≤ 1 / B := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hcontA : Continuous (dampedGaussian (abelCoefficient B)) := by
    unfold dampedGaussian
    fun_prop
  have hcontF : Continuous (dampedGaussian (-Complex.I)) := by
    unfold dampedGaussian
    fun_prop
  unfold fresnelPartial
  rw [← intervalIntegral.integral_sub
    (hcontA.intervalIntegrable 0 B) (hcontF.intervalIntegrable 0 B)]
  calc
    ‖∫ x in (0 : ℝ)..B,
        dampedGaussian (abelCoefficient B) x -
          dampedGaussian (-Complex.I) x‖ ≤
        ∫ _x in (0 : ℝ)..B, 1 / B ^ 2 := by
      apply intervalIntegral.norm_integral_le_of_norm_le hBpos.le
      · exact Eventually.of_forall fun x hx =>
          norm_abel_damped_sub_fresnel_le hB hx.1.le hx.2
      · exact intervalIntegrable_const
    _ = 1 / B := by
      simp [hBpos.ne']
      field_simp

private theorem abelCoefficient_re_pos {B : ℝ} (hB : 1 ≤ B) :
    0 < (abelCoefficient B).re := by
  unfold abelCoefficient
  rw [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero]
  positivity

private theorem abelCoefficient_norm_ge_one (B : ℝ) :
    1 ≤ ‖abelCoefficient B‖ := by
  have him : (abelCoefficient B).im = -1 := by
    unfold abelCoefficient
    rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im]
    ring
  calc
    1 = |(abelCoefficient B).im| := by rw [him, abs_neg, abs_one]
    _ ≤ ‖abelCoefficient B‖ := Complex.abs_im_le_norm _

private theorem norm_gaussianHalf_abel_sub_fresnelPartial_le
    {B : ℝ} (hB : 1 ≤ B) :
    ‖gaussianHalf (abelCoefficient B) - fresnelPartial B‖ ≤ 2 / B := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  calc
    ‖gaussianHalf (abelCoefficient B) - fresnelPartial B‖ ≤
        ‖gaussianHalf (abelCoefficient B) -
            ∫ x in (0 : ℝ)..B, dampedGaussian (abelCoefficient B) x‖ +
          ‖(∫ x in (0 : ℝ)..B, dampedGaussian (abelCoefficient B) x) -
            fresnelPartial B‖ := by
      rw [show gaussianHalf (abelCoefficient B) - fresnelPartial B =
        (gaussianHalf (abelCoefficient B) -
          ∫ x in (0 : ℝ)..B, dampedGaussian (abelCoefficient B) x) +
        ((∫ x in (0 : ℝ)..B, dampedGaussian (abelCoefficient B) x) -
          fresnelPartial B) by ring]
      exact norm_add_le _ _
    _ ≤ 1 / B + 1 / B := add_le_add
      (norm_gaussianHalf_sub_partial_le
        (abelCoefficient_re_pos hB) (abelCoefficient_norm_ge_one B) hBpos)
      (norm_abel_partial_sub_fresnelPartial_le hB)
    _ = 2 / B := by ring

private theorem tendsto_gaussianHalf_abel_sub_fresnelPartial :
    Tendsto (fun B : ℝ =>
      gaussianHalf (abelCoefficient B) - fresnelPartial B)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Eventually.of_forall fun B => norm_nonneg
      (gaussianHalf (abelCoefficient B) - fresnelPartial B))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    exact norm_gaussianHalf_abel_sub_fresnelPartial_le hB
  · simpa [div_eq_mul_inv] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun B : ℝ => B⁻¹)
        atTop (𝓝 0))

private theorem tendsto_abelCoefficient :
    Tendsto abelCoefficient atTop (𝓝 (-Complex.I)) := by
  have hinv :
      Tendsto (fun B : ℝ => 1 / B ^ 4) atTop (𝓝 0) := by
    simpa [one_div, inv_pow] using
      (tendsto_inv_atTop_zero.pow 4 :
        Tendsto (fun B : ℝ => B⁻¹ ^ 4) atTop (𝓝 (0 ^ 4)))
  unfold abelCoefficient
  convert
    hinv.ofReal.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => Complex.I) atTop (𝓝 Complex.I)) using 1
  norm_num

private theorem pi_div_neg_I_mem_slitPlane :
    ((Real.pi : ℂ) / (-Complex.I)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  have heq : (Real.pi : ℂ) / (-Complex.I) =
      (Real.pi : ℂ) * Complex.I := by
    apply (div_eq_iff (by simp : -Complex.I ≠ 0)).2
    simp [mul_assoc]
  rw [heq, Complex.mul_im]
  simp [Real.pi_ne_zero]

private theorem tendsto_gaussianHalf_abel :
    Tendsto (fun B : ℝ => gaussianHalf (abelCoefficient B))
      atTop (𝓝 (gaussianHalf (-Complex.I))) := by
  have hbase :
      Tendsto (fun B : ℝ => (Real.pi : ℂ) / abelCoefficient B)
        atTop (𝓝 ((Real.pi : ℂ) / (-Complex.I))) :=
    tendsto_const_nhds.div tendsto_abelCoefficient (by simp)
  have hpow :
      Tendsto
        (fun B : ℝ =>
          ((Real.pi : ℂ) / abelCoefficient B) ^ (1 / 2 : ℂ))
        atTop
        (𝓝 (((Real.pi : ℂ) / (-Complex.I)) ^ (1 / 2 : ℂ))) :=
    hbase.cpow tendsto_const_nhds pi_div_neg_I_mem_slitPlane
  simpa [gaussianHalf] using hpow.div_const 2

private theorem tendsto_fresnelPartial_gaussianHalf :
    Tendsto fresnelPartial atTop (𝓝 (gaussianHalf (-Complex.I))) := by
  have h :=
    tendsto_gaussianHalf_abel.sub
      tendsto_gaussianHalf_abel_sub_fresnelPartial
  convert h using 1
  · funext B
    ring
  · simp

private theorem pi_div_neg_I_eq_pi_mul_I :
    (Real.pi : ℂ) / (-Complex.I) = (Real.pi : ℂ) * Complex.I := by
  apply (div_eq_iff (by simp : -Complex.I ≠ 0)).2
  simp [mul_assoc]

private theorem gaussianHalf_neg_I_re :
    (gaussianHalf (-Complex.I)).re = Real.sqrt (Real.pi / 2) / 2 := by
  unfold gaussianHalf
  rw [Complex.div_re]
  norm_num
  rw [pi_div_neg_I_eq_pi_mul_I]
  have h :=
    Complex.cpow_inv_two_re ((Real.pi : ℂ) * Complex.I)
  have hhalf : (1 / 2 : ℂ) = (2⁻¹ : ℂ) := by norm_num
  rw [hhalf]
  rw [h]
  simp [Complex.norm_mul, Real.pi_pos.le, abs_of_pos Real.pi_pos]
  ring

private theorem gaussianHalf_neg_I_im :
    (gaussianHalf (-Complex.I)).im = Real.sqrt (Real.pi / 2) / 2 := by
  unfold gaussianHalf
  rw [Complex.div_im]
  norm_num
  rw [pi_div_neg_I_eq_pi_mul_I]
  have himnonneg : 0 ≤ ((Real.pi : ℂ) * Complex.I).im := by
    simp [Real.pi_pos.le]
  have h :=
    Complex.cpow_inv_two_im_eq_sqrt himnonneg
  have hhalf : (1 / 2 : ℂ) = (2⁻¹ : ℂ) := by norm_num
  rw [hhalf]
  rw [h]
  simp [Complex.norm_mul, Real.pi_pos.le, abs_of_pos Real.pi_pos]
  ring

private theorem dampedGaussian_neg_I_re (x : ℝ) :
    (dampedGaussian (-Complex.I) x).re = Real.cos (x ^ 2) := by
  unfold dampedGaussian
  rw [show -(-Complex.I) * (x : ℂ) ^ 2 =
      ((x ^ 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re (x ^ 2)

private theorem dampedGaussian_neg_I_im (x : ℝ) :
    (dampedGaussian (-Complex.I) x).im = Real.sin (x ^ 2) := by
  unfold dampedGaussian
  rw [show -(-Complex.I) * (x : ℂ) ^ 2 =
      ((x ^ 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im (x ^ 2)

private theorem fresnelPartial_re (B : ℝ) :
    (fresnelPartial B).re =
      ∫ x in (0 : ℝ)..B, Real.cos (x ^ 2) := by
  have hcont : Continuous (dampedGaussian (-Complex.I)) := by
    unfold dampedGaussian
    fun_prop
  unfold fresnelPartial
  calc
    (∫ x in (0 : ℝ)..B, dampedGaussian (-Complex.I) x).re =
        ∫ x in (0 : ℝ)..B, (dampedGaussian (-Complex.I) x).re := by
      exact (Complex.reCLM.intervalIntegral_comp_comm
        (hcont.intervalIntegrable 0 B)).symm
    _ = ∫ x in (0 : ℝ)..B, Real.cos (x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact dampedGaussian_neg_I_re x

private theorem fresnelPartial_im (B : ℝ) :
    (fresnelPartial B).im =
      ∫ x in (0 : ℝ)..B, Real.sin (x ^ 2) := by
  have hcont : Continuous (dampedGaussian (-Complex.I)) := by
    unfold dampedGaussian
    fun_prop
  unfold fresnelPartial
  calc
    (∫ x in (0 : ℝ)..B, dampedGaussian (-Complex.I) x).im =
        ∫ x in (0 : ℝ)..B, (dampedGaussian (-Complex.I) x).im := by
      exact (Complex.imCLM.intervalIntegral_comp_comm
        (hcont.intervalIntegrable 0 B)).symm
    _ = ∫ x in (0 : ℝ)..B, Real.sin (x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact dampedGaussian_neg_I_im x

private theorem sqrt_pi_div_two_div_two :
    Real.sqrt (Real.pi / 2) / 2 =
      Real.sqrt Real.pi / (2 * Real.sqrt 2) := by
  rw [Real.sqrt_div Real.pi_pos.le]
  ring

private theorem tendsto_fresnel_cos :
    Tendsto (fun B : ℝ => ∫ x in (0 : ℝ)..B, Real.cos (x ^ 2))
      atTop (𝓝 (Real.sqrt Real.pi / (2 * Real.sqrt 2))) := by
  have h :=
    (Complex.continuous_re.tendsto
      (gaussianHalf (-Complex.I))).comp
      tendsto_fresnelPartial_gaussianHalf
  have h' :
      Tendsto (fun B : ℝ => (fresnelPartial B).re)
        atTop (𝓝 ((gaussianHalf (-Complex.I)).re)) := by
    simpa only [Function.comp_apply] using h
  rw [gaussianHalf_neg_I_re, sqrt_pi_div_two_div_two] at h'
  exact h'.congr' (Eventually.of_forall fun B => fresnelPartial_re B)

private theorem tendsto_fresnel_sin :
    Tendsto (fun B : ℝ => ∫ x in (0 : ℝ)..B, Real.sin (x ^ 2))
      atTop (𝓝 (Real.sqrt Real.pi / (2 * Real.sqrt 2))) := by
  have h :=
    (Complex.continuous_im.tendsto
      (gaussianHalf (-Complex.I))).comp
      tendsto_fresnelPartial_gaussianHalf
  have h' :
      Tendsto (fun B : ℝ => (fresnelPartial B).im)
        atTop (𝓝 ((gaussianHalf (-Complex.I)).im)) := by
    simpa only [Function.comp_apply] using h
  rw [gaussianHalf_neg_I_im, sqrt_pi_div_two_div_two] at h'
  exact h'.congr' (Eventually.of_forall fun B => fresnelPartial_im B)

private def invSqrt (x : ℝ) : ℝ :=
  x ^ (-(1 : ℝ) / 2)

private theorem invSqrt_eq_one_div_sqrt {x : ℝ} (hx : 0 ≤ x) :
    invSqrt x = 1 / Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [invSqrt]
  · rw [invSqrt, show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hx.le, Real.sqrt_eq_rpow]
    simp only [one_div]

private theorem integrableOn_one_div_sqrt_Icc
    {C : ℝ} (hC : 0 ≤ C) :
    IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Icc 0 C) := by
  have hrpow :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
        volume 0 C :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hrpowOn :
      IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
        (Icc 0 C) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hC).1 hrpow
  refine hrpowOn.congr_fun ?_ measurableSet_Icc
  intro x hx
  exact invSqrt_eq_one_div_sqrt hx.1

private theorem square_substitution
    (h : ℝ → ℝ) (hcont : Continuous h) {B : ℝ} (hB : 0 ≤ B) :
    (∫ x in (0 : ℝ)..B ^ 2, h x / Real.sqrt x) =
      2 * ∫ t in (0 : ℝ)..B, h (t ^ 2) := by
  let g : ℝ → ℝ := fun x => h x / Real.sqrt x
  have hBsq : 0 ≤ B ^ 2 := sq_nonneg B
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) (B ^ 2)) := by
    have hprod :
        IntegrableOn (fun x : ℝ => (1 / Real.sqrt x) * h x)
          (Icc (0 : ℝ) (B ^ 2)) :=
      (integrableOn_one_div_sqrt_Icc hBsq).mul_continuousOn
        hcont.continuousOn isCompact_Icc
    refine hprod.congr_fun ?_ measurableSet_Icc
    intro x _
    dsimp [g]
    ring
  have hfcont :
      ContinuousOn (fun t : ℝ => t ^ 2) [[(0 : ℝ), B]] := by
    fun_prop
  have hfder :
      ∀ t ∈ Ioo (min (0 : ℝ) B) (max (0 : ℝ) B),
        HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * t) (Ioi t) t := by
    intro t _
    convert ((hasDerivAt_id t).pow 2).hasDerivWithinAt using 1 <;>
      simp <;> ring
  have hgcont :
      ContinuousOn g
        ((fun t : ℝ => t ^ 2) ''
          Ioo (min (0 : ℝ) B) (max (0 : ℝ) B)) := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    rw [min_eq_left hB, max_eq_right hB] at ht
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht.1
    have hsqrt_ne : Real.sqrt (t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.2 ht2).ne'
    have hcontinuous : ContinuousAt g (t ^ 2) := by
      dsimp [g]
      apply ContinuousAt.div
      · exact hcont.continuousAt
      · fun_prop
      · exact hsqrt_ne
    exact hcontinuous.continuousWithinAt
  have hgimage :
      IntegrableOn g
        ((fun t : ℝ => t ^ 2) '' [[(0 : ℝ), B]]) := by
    refine hgIcc.mono_set ?_
    rintro z ⟨t, ht, rfl⟩
    rw [uIcc_of_le hB] at ht
    exact ⟨sq_nonneg t,
      by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]⟩
  have hgood :
      IntegrableOn (fun t : ℝ => 2 * h (t ^ 2))
        (Icc (0 : ℝ) B) := by
    exact (continuous_const.mul (hcont.comp (continuous_id.pow 2))).integrableOn_Icc
  have hcompIcc :
      IntegrableOn
        (fun t : ℝ => (g ∘ fun u : ℝ => u ^ 2) t * (2 * t))
        (Icc (0 : ℝ) B) := by
    refine hgood.congr ?_
    filter_upwards
      [ae_restrict_mem measurableSet_Icc,
        (volume.ae_ne (0 : ℝ)).filter_mono
          (ae_mono Measure.restrict_le_self)] with t htI ht
    have htpos : 0 < t :=
      lt_of_le_of_ne htI.1 (Ne.symm ht)
    dsimp [g, Function.comp_apply]
    rw [Real.sqrt_sq htpos.le]
    field_simp [htpos.ne']
  have hcomp :
      IntegrableOn
        (fun t : ℝ => (g ∘ fun u : ℝ => u ^ 2) t * (2 * t))
        [[(0 : ℝ), B]] := by
    simpa [uIcc_of_le hB] using hcompIcc
  have hsubst :
      (∫ t in (0 : ℝ)..B,
          (g ∘ fun u : ℝ => u ^ 2) t * (2 * t)) =
        ∫ x in (0 : ℝ)..B ^ 2, g x := by
    simpa using
      (intervalIntegral.integral_comp_mul_deriv'''
        (a := (0 : ℝ)) (b := B)
        (f := fun t : ℝ => t ^ 2) (f' := fun t : ℝ => 2 * t)
        (g := g) hfcont hfder hgcont hgimage hcomp)
  have hpoint :
      (∫ t in (0 : ℝ)..B,
          (g ∘ fun u : ℝ => u ^ 2) t * (2 * t)) =
        ∫ t in (0 : ℝ)..B, 2 * h (t ^ 2) := by
    refine intervalIntegral.integral_congr_ae' ?_ ?_
    · filter_upwards with t
      intro ht
      have htpos : 0 < t := ht.1
      dsimp [g, Function.comp_apply]
      rw [Real.sqrt_sq htpos.le]
      field_simp [htpos.ne']
    · filter_upwards with t
      intro ht
      exfalso
      linarith [ht.1, ht.2]
  change (∫ x in (0 : ℝ)..B ^ 2, g x) =
    2 * ∫ t in (0 : ℝ)..B, h (t ^ 2)
  rw [← hsubst, hpoint, intervalIntegral.integral_const_mul]

private theorem twice_fresnel_value :
    2 * (Real.sqrt Real.pi / (2 * Real.sqrt 2)) =
      Real.sqrt (Real.pi / 2) := by
  rw [Real.sqrt_div Real.pi_pos.le]
  ring

private theorem tendsto_weighted_sin :
    Tendsto
      (fun B : ℝ => ∫ x in (0 : ℝ)..B,
        Real.sin x / Real.sqrt x)
      atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have hcomp :=
    tendsto_fresnel_sin.comp Real.tendsto_sqrt_atTop
  have hmul :
      Tendsto
        (fun B : ℝ =>
          2 * ∫ t in (0 : ℝ)..Real.sqrt B, Real.sin (t ^ 2))
        atTop
        (𝓝 (2 * (Real.sqrt Real.pi / (2 * Real.sqrt 2)))) :=
    tendsto_const_nhds.mul hcomp
  rw [twice_fresnel_value] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
  exact (square_substitution Real.sin Real.continuous_sin
    (Real.sqrt_nonneg B)).symm.trans (by rw [Real.sq_sqrt hB])

private theorem tendsto_weighted_cos :
    Tendsto
      (fun B : ℝ => ∫ x in (0 : ℝ)..B,
        Real.cos x / Real.sqrt x)
      atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have hcomp :=
    tendsto_fresnel_cos.comp Real.tendsto_sqrt_atTop
  have hmul :
      Tendsto
        (fun B : ℝ =>
          2 * ∫ t in (0 : ℝ)..Real.sqrt B, Real.cos (t ^ 2))
        atTop
        (𝓝 (2 * (Real.sqrt Real.pi / (2 * Real.sqrt 2)))) :=
    tendsto_const_nhds.mul hcomp
  rw [twice_fresnel_value] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
  exact (square_substitution Real.cos Real.continuous_cos
    (Real.sqrt_nonneg B)).symm.trans (by rw [Real.sq_sqrt hB])
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

private theorem improperIntegral_eq_of_tendsto
    {a L : ℝ} {f : ℝ → ℝ}
    (h : Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (𝓝 L)) :
    improperIntegral a f = L := by
  unfold improperIntegral HasImproperIntegral
  have hset :
      {K : ℝ |
          Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (𝓝 K)} =
        {L} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hK
      exact tendsto_nhds_unique hK h
    · rintro rfl
      exact h
  rw [hset]
  exact csInf_singleton L

private theorem improperIntegral_fresnel_sin :
    improperIntegral 0 (fun x => Real.sin (x ^ 2)) =
      Real.sqrt Real.pi / (2 * Real.sqrt 2) :=
  improperIntegral_eq_of_tendsto tendsto_fresnel_sin

private theorem improperIntegral_weighted_sin :
    improperIntegral 0 (fun x => Real.sin x / Real.sqrt x) =
      Real.sqrt (Real.pi / 2) :=
  improperIntegral_eq_of_tendsto tendsto_weighted_sin

private theorem improperIntegral_fresnel_cos :
    improperIntegral 0 (fun x => Real.cos (x ^ 2)) =
      Real.sqrt Real.pi / (2 * Real.sqrt 2) :=
  improperIntegral_eq_of_tendsto tendsto_fresnel_cos

private theorem improperIntegral_weighted_cos :
    improperIntegral 0 (fun x => Real.cos x / Real.sqrt x) =
      Real.sqrt (Real.pi / 2) :=
  improperIntegral_eq_of_tendsto tendsto_weighted_cos

private theorem tendsto_gaussian_interval {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun b : ℝ => ∫ y in (0 : ℝ)..b, Real.exp (-c * y ^ 2))
      atTop (𝓝 (Real.sqrt (Real.pi / c) / 2)) := by
  have h :=
    intervalIntegral_tendsto_integral_Ioi 0
      ((integrableOn_Ioi_exp_neg_mul_sq_iff).2 hc) tendsto_id
  rw [integral_gaussian_Ioi c] at h
  exact h

private theorem improperIntegral_const_mul_gaussian
    (s : ℝ) {c : ℝ} (hc : 0 < c) :
    improperIntegral 0 (fun y => s * Real.exp (-c * y ^ 2)) =
      s * (Real.sqrt (Real.pi / c) / 2) := by
  apply improperIntegral_eq_of_tendsto
  have hconst : Tendsto (fun _ : ℝ => s) atTop (𝓝 s) :=
    tendsto_const_nhds
  have h := hconst.mul (tendsto_gaussian_interval hc)
  simpa only [intervalIntegral.integral_const_mul] using h

private theorem improperIntegral_eq_integral_Ioi
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    improperIntegral 0 f = ∫ y in Ioi (0 : ℝ), f y :=
  improperIntegral_eq_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id)

private theorem integrable_quarticKernel :
    Integrable (fun y : ℝ => 1 / (1 + y ^ 4)) := by
  apply Integrable.mono'
      (integrable_inv_one_add_sq.const_mul (2 : ℝ))
  · exact
      (continuous_const.div
        (continuous_const.add (continuous_id.pow 4))
        (fun y => by
          change 1 + y ^ 4 ≠ 0
          positivity)).aestronglyMeasurable
  · filter_upwards with y
    have h2 : 0 < 1 + y ^ 2 := by positivity
    have h4 : 0 < 1 + y ^ 4 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr h4)]
    change 1 / (1 + y ^ 4) ≤ 2 * (1 + y ^ 2)⁻¹
    field_simp [h2.ne', h4.ne']
    nlinarith [sq_nonneg (2 * y ^ 2 - 1), sq_nonneg y]

private theorem integrable_rationalTwo :
    Integrable (fun y : ℝ => y ^ 2 / (1 + y ^ 4)) := by
  apply Integrable.mono'
      (integrable_inv_one_add_sq.const_mul (2 : ℝ))
  · exact
      ((continuous_id.pow 2).div
        (continuous_const.add (continuous_id.pow 4))
        (fun y => by
          change 1 + y ^ 4 ≠ 0
          positivity)).aestronglyMeasurable
  · filter_upwards with y
    have h2 : 0 < 1 + y ^ 2 := by positivity
    have h4 : 0 < 1 + y ^ 4 := by positivity
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg y) h4.le)]
    change y ^ 2 / (1 + y ^ 4) ≤ 2 * (1 + y ^ 2)⁻¹
    field_simp [h2.ne', h4.ne']
    nlinarith [sq_nonneg (2 * y ^ 2 - 1), sq_nonneg y]

private theorem integrable_kernelZero {c : ℝ} (hc : 0 < c) :
    Integrable
      (fun y : ℝ => Real.exp (-c * y ^ 2) / (1 + y ^ 4)) := by
  apply Integrable.mono' (integrable_exp_neg_mul_sq hc)
  · exact
      ((Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.pow 2))).div
        (continuous_const.add (continuous_id.pow 4))
        (fun y => by
          change 1 + y ^ 4 ≠ 0
          positivity)).aestronglyMeasurable
  · filter_upwards with y
    have hden : 0 < 1 + y ^ 4 := by positivity
    rw [Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.exp_pos _) hden)]
    rw [div_le_iff₀ hden]
    exact le_mul_of_one_le_right (Real.exp_nonneg _)
      (by nlinarith [sq_nonneg (y ^ 2)])

private theorem integrable_kernelTwo {c : ℝ} (hc : 0 < c) :
    Integrable
      (fun y : ℝ =>
        y ^ 2 * Real.exp (-c * y ^ 2) / (1 + y ^ 4)) := by
  apply Integrable.mono' (integrable_exp_neg_mul_sq hc)
  · exact
      (((continuous_id.pow 2).mul
          (Real.continuous_exp.comp
            (continuous_const.mul (continuous_id.pow 2)))).div
        (continuous_const.add (continuous_id.pow 4))
        (fun y => by
          change 1 + y ^ 4 ≠ 0
          positivity)).aestronglyMeasurable
  · filter_upwards with y
    have hden : 0 < 1 + y ^ 4 := by positivity
    have hnum : 0 ≤ y ^ 2 * Real.exp (-c * y ^ 2) :=
      mul_nonneg (sq_nonneg y) (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden.le)]
    rw [div_le_iff₀ hden]
    have hy : y ^ 2 ≤ 1 + y ^ 4 := by
      nlinarith [sq_nonneg (y ^ 2 - 1)]
    calc
      y ^ 2 * Real.exp (-c * y ^ 2) ≤
          (1 + y ^ 4) * Real.exp (-c * y ^ 2) :=
        mul_le_mul_of_nonneg_right hy (Real.exp_nonneg _)
      _ = Real.exp (-c * y ^ 2) * (1 + y ^ 4) := by ring

private def oscillatoryPrimitive (y x : ℝ) : ℝ :=
  -((y ^ 2 * Real.sin x + Real.cos x) *
      Real.exp (-x * y ^ 2) / (1 + y ^ 4))

private theorem hasDerivAt_oscillatoryPrimitive (y x : ℝ) :
    HasDerivAt (oscillatoryPrimitive y)
      (Real.sin x * Real.exp (-x * y ^ 2)) x := by
  have htrig :
      HasDerivAt (fun t : ℝ => y ^ 2 * Real.sin t + Real.cos t)
        (y ^ 2 * Real.cos x - Real.sin x) x := by
    convert
      ((Real.hasDerivAt_sin x).const_mul (y ^ 2)).add
        (Real.hasDerivAt_cos x) using 1 <;> ring
  have hinner :
      HasDerivAt (fun t : ℝ => -t * y ^ 2) (-y ^ 2) x := by
    convert (hasDerivAt_id x).neg.mul_const (y ^ 2) using 1 <;> ring
  have hexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t * y ^ 2))
        ((-y ^ 2) * Real.exp (-x * y ^ 2)) x :=
    by
      convert (Real.hasDerivAt_exp _).comp x hinner using 1 <;>
        simp [Function.comp_def] <;> ring
  have h :=
    ((htrig.mul hexp).div_const (1 + y ^ 4)).neg
  convert h using 1
  have hden : 1 + y ^ 4 ≠ 0 := by positivity
  field_simp [hden]
  ring

private theorem intervalIntegral_sin_mul_gaussian
    (a b y : ℝ) :
    (∫ x in a..b, Real.sin x * Real.exp (-x * y ^ 2)) =
      Real.sin a *
          (y ^ 2 * Real.exp (-a * y ^ 2) / (1 + y ^ 4)) +
        Real.cos a *
          (Real.exp (-a * y ^ 2) / (1 + y ^ 4)) -
        Real.sin b *
          (y ^ 2 * Real.exp (-b * y ^ 2) / (1 + y ^ 4)) -
        Real.cos b *
          (Real.exp (-b * y ^ 2) / (1 + y ^ 4)) := by
  have hfund :
      (∫ x in a..b, Real.sin x * Real.exp (-x * y ^ 2)) =
        oscillatoryPrimitive y b - oscillatoryPrimitive y a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_oscillatoryPrimitive y x)
      ((Real.continuous_sin.mul
        (Real.continuous_exp.comp
          (continuous_id.neg.mul continuous_const))).intervalIntegrable a b)
  rw [hfund]
  unfold oscillatoryPrimitive
  ring

private theorem integrable_sin_mul_gaussian_rectangle
    {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) (h01 : x₀ ≤ x₁) :
    Integrable
      (fun z : ℝ × ℝ =>
        Real.sin z.1 * Real.exp (-z.1 * z.2 ^ 2))
      ((volume.restrict (uIoc x₀ x₁)).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hx :
      Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (uIoc x₀ x₁)) := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIoc x₀ x₁)
    exact integrableOn_const (C := (1 : ℝ))
      (by
        rw [Real.volume_uIoc]
        finiteness)
      (by norm_num)
  have hy :
      Integrable (fun y : ℝ => Real.exp (-x₀ * y ^ 2))
        (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_exp_neg_mul_sq hx₀).integrableOn
  apply Integrable.mono' (hx.mul_prod hy)
  · have hcont :
        Continuous
          (fun z : ℝ × ℝ =>
            Real.sin z.1 * Real.exp (-z.1 * z.2 ^ 2)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  · have hmem :
        ∀ᵐ z ∂((volume.restrict (uIoc x₀ x₁)).prod
            (volume.restrict (Ioi (0 : ℝ)))),
          z ∈ uIoc x₀ x₁ ×ˢ Ioi (0 : ℝ) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem
        (measurableSet_uIoc.prod measurableSet_Ioi)
    filter_upwards [hmem] with z hz
    rw [uIoc_of_le h01] at hz
    change
      ‖Real.sin z.1 * Real.exp (-z.1 * z.2 ^ 2)‖ ≤
        1 * Real.exp (-x₀ * z.2 ^ 2)
    rw [one_mul, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |Real.sin z.1| * Real.exp (-z.1 * z.2 ^ 2) ≤
          1 * Real.exp (-z.1 * z.2 ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one z.1)
          (Real.exp_pos _).le
      _ ≤ Real.exp (-x₀ * z.2 ^ 2) := by
        convert
          Real.exp_le_exp.mpr
            (neg_le_neg
              (mul_le_mul_of_nonneg_right hz.1.1.le
                (sq_nonneg z.2))) using 1 <;> ring

private theorem improperIntegral_interval_sin_mul_gaussian
    {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) (h01 : x₀ ≤ x₁) :
    improperIntegral 0
        (fun y =>
          ∫ x in x₀..x₁,
            Real.sin x * Real.exp (-x * y ^ 2)) =
      Real.sin x₀ *
          improperIntegral 0
            (fun y =>
              y ^ 2 * Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) +
        Real.cos x₀ *
          improperIntegral 0
            (fun y =>
              Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) -
        Real.sin x₁ *
          improperIntegral 0
            (fun y =>
              y ^ 2 * Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) -
        Real.cos x₁ *
          improperIntegral 0
            (fun y =>
              Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) := by
  have hx₁ : 0 < x₁ := hx₀.trans_le h01
  have h20 :
      IntegrableOn
        (fun y : ℝ =>
          y ^ 2 * Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4))
        (Ioi (0 : ℝ)) :=
    (integrable_kernelTwo hx₀).integrableOn
  have h00 :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4))
        (Ioi (0 : ℝ)) :=
    (integrable_kernelZero hx₀).integrableOn
  have h21 :
      IntegrableOn
        (fun y : ℝ =>
          y ^ 2 * Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4))
        (Ioi (0 : ℝ)) :=
    (integrable_kernelTwo hx₁).integrableOn
  have h01' :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4))
        (Ioi (0 : ℝ)) :=
    (integrable_kernelZero hx₁).integrableOn
  have hrect :=
    integrable_sin_mul_gaussian_rectangle hx₀ h01
  have hinner :
      IntegrableOn
        (fun y : ℝ =>
          ∫ x in x₀..x₁,
            Real.sin x * Real.exp (-x * y ^ 2))
        (Ioi (0 : ℝ)) := by
    change
      Integrable
        (fun y : ℝ =>
          ∫ x in x₀..x₁,
            Real.sin x * Real.exp (-x * y ^ 2))
        (volume.restrict (Ioi (0 : ℝ)))
    simpa only [intervalIntegral.integral_of_le h01,
      uIoc_of_le h01] using hrect.integral_prod_right
  rw [improperIntegral_eq_integral_Ioi hinner,
    improperIntegral_eq_integral_Ioi h20,
    improperIntegral_eq_integral_Ioi h00,
    improperIntegral_eq_integral_Ioi h21,
    improperIntegral_eq_integral_Ioi h01']
  calc
    (∫ y in Ioi (0 : ℝ),
        ∫ x in x₀..x₁,
          Real.sin x * Real.exp (-x * y ^ 2)) =
      ∫ y in Ioi (0 : ℝ),
        (Real.sin x₀ *
            (y ^ 2 * Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) +
          Real.cos x₀ *
            (Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) -
          Real.sin x₁ *
            (y ^ 2 * Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) -
          Real.cos x₁ *
            (Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4))) := by
      apply integral_congr_ae
      filter_upwards with y
      exact intervalIntegral_sin_mul_gaussian x₀ x₁ y
    _ = _ := by
      let A : ℝ → ℝ := fun y =>
        Real.sin x₀ *
          (y ^ 2 * Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4))
      let B : ℝ → ℝ := fun y =>
        Real.cos x₀ *
          (Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4))
      let C : ℝ → ℝ := fun y =>
        Real.sin x₁ *
          (y ^ 2 * Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4))
      let D : ℝ → ℝ := fun y =>
        Real.cos x₁ *
          (Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4))
      have hA : IntegrableOn A (Ioi (0 : ℝ)) := h20.const_mul _
      have hB : IntegrableOn B (Ioi (0 : ℝ)) := h00.const_mul _
      have hC : IntegrableOn C (Ioi (0 : ℝ)) := h21.const_mul _
      have hD : IntegrableOn D (Ioi (0 : ℝ)) := h01'.const_mul _
      change
        (∫ y in Ioi (0 : ℝ), ((A y + B y) - C y) - D y) =
          _
      have hDsplit :
          (∫ y in Ioi (0 : ℝ), ((A y + B y) - C y) - D y) =
            (∫ y in Ioi (0 : ℝ), (A y + B y) - C y) -
              ∫ y in Ioi (0 : ℝ), D y := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_sub ((hA.add hB).sub hC) hD)
      have hCsplit :
          (∫ y in Ioi (0 : ℝ), (A y + B y) - C y) =
            (∫ y in Ioi (0 : ℝ), A y + B y) -
              ∫ y in Ioi (0 : ℝ), C y := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_sub (hA.add hB) hC)
      have hABsplit :
          (∫ y in Ioi (0 : ℝ), A y + B y) =
            (∫ y in Ioi (0 : ℝ), A y) +
              ∫ y in Ioi (0 : ℝ), B y := by
        simpa only [Pi.add_apply] using integral_add hA hB
      rw [hDsplit, hCsplit, hABsplit]
      simp only [A, B, C, D, integral_const_mul]

private def epsilon (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

private theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by
  unfold epsilon
  positivity

private theorem tendsto_epsilon :
    Tendsto epsilon atTop (𝓝 0) := by
  unfold epsilon
  exact
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))

private theorem tendsto_kernelZero_integrals :
    Tendsto
      (fun n : ℕ =>
        ∫ y in Ioi (0 : ℝ),
          Real.exp (-epsilon n * y ^ 2) / (1 + y ^ 4))
      atTop
      (𝓝 (∫ y in Ioi (0 : ℝ), 1 / (1 + y ^ 4))) := by
  apply tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun y : ℝ => 1 / (1 + y ^ 4))
  · intro n
    exact
      ((Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.pow 2))).div
        (continuous_const.add (continuous_id.pow 4))
        (fun y => by
          change 1 + y ^ 4 ≠ 0
          positivity)).aestronglyMeasurable
  · exact integrable_quarticKernel.integrableOn
  · intro n
    filter_upwards with y
    have hden : 0 < 1 + y ^ 4 := by positivity
    rw [Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.exp_pos _) hden)]
    apply (div_le_div_iff_of_pos_right hden).2
    apply (Real.exp_le_one_iff).2
    convert neg_nonpos.mpr
      (mul_nonneg (epsilon_pos n).le (sq_nonneg y)) using 1 <;>
      ring
  · filter_upwards with y
    have harg :
        Tendsto (fun n : ℕ => -epsilon n * y ^ 2)
          atTop (𝓝 0) := by
      convert tendsto_epsilon.neg.mul_const (y ^ 2) using 1 <;> simp
    have hexp :
        Tendsto (fun n : ℕ => Real.exp (-epsilon n * y ^ 2))
          atTop (𝓝 1) := by
      simpa using Real.continuous_exp.continuousAt.tendsto.comp harg
    convert hexp.div_const (1 + y ^ 4) using 1 <;> simp

private theorem tendsto_sin_kernelTwo_integrals :
    Tendsto
      (fun n : ℕ =>
        ∫ y in Ioi (0 : ℝ),
          Real.sin (epsilon n) *
            (y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
              (1 + y ^ 4)))
      atTop (𝓝 0) := by
  have h :
      Tendsto
        (fun n : ℕ =>
          ∫ y in Ioi (0 : ℝ),
            Real.sin (epsilon n) *
              (y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                (1 + y ^ 4)))
        atTop
        (𝓝 (∫ _y in Ioi (0 : ℝ), (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun _ : ℝ => 0)
      (fun y : ℝ => y ^ 2 / (1 + y ^ 4))
    · intro n
      exact
        ((Real.continuous_sin.comp continuous_const).mul
          (((continuous_id.pow 2).mul
            (Real.continuous_exp.comp
              (continuous_const.mul (continuous_id.pow 2)))).div
            (continuous_const.add (continuous_id.pow 4))
            (fun y => by
              change 1 + y ^ 4 ≠ 0
              positivity))).aestronglyMeasurable
    · exact integrable_rationalTwo.integrableOn
    · intro n
      filter_upwards with y
      have hden : 0 < 1 + y ^ 4 := by positivity
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg
          (div_nonneg
            (mul_nonneg (sq_nonneg y) (Real.exp_nonneg _)) hden.le)]
      calc
        |Real.sin (epsilon n)| *
            (y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
              (1 + y ^ 4)) ≤
            1 *
              (y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                (1 + y ^ 4)) :=
          mul_le_mul_of_nonneg_right
            (Real.abs_sin_le_one (epsilon n))
            (div_nonneg
              (mul_nonneg (sq_nonneg y) (Real.exp_nonneg _)) hden.le)
        _ ≤ y ^ 2 / (1 + y ^ 4) := by
          rw [one_mul]
          apply (div_le_div_iff_of_pos_right hden).2
          exact mul_le_of_le_one_right (sq_nonneg y)
            ((Real.exp_le_one_iff).2
              (by
                convert neg_nonpos.mpr
                  (mul_nonneg (epsilon_pos n).le (sq_nonneg y))
                    using 1 <;> ring))
    · filter_upwards with y
      have hsin :
          Tendsto (fun n : ℕ => Real.sin (epsilon n))
            atTop (𝓝 0) := by
        simpa using Real.continuous_sin.continuousAt.tendsto.comp
          tendsto_epsilon
      have harg :
          Tendsto (fun n : ℕ => -epsilon n * y ^ 2)
            atTop (𝓝 0) := by
        convert tendsto_epsilon.neg.mul_const (y ^ 2) using 1 <;> simp
      have hk :
          Tendsto
            (fun n : ℕ =>
              y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                (1 + y ^ 4))
            atTop
            (𝓝 (y ^ 2 / (1 + y ^ 4))) := by
        have hexp :
            Tendsto (fun n : ℕ => Real.exp (-epsilon n * y ^ 2))
              atTop (𝓝 1) := by
          simpa using Real.continuous_exp.continuousAt.tendsto.comp harg
        convert
          (tendsto_const_nhds.mul hexp).div_const (1 + y ^ 4)
            using 1 <;> simp
      simpa using hsin.mul hk
  simpa using h

private theorem abs_improperIntegral_kernelZero_le
    {c : ℝ} (hc : 0 < c) :
    |improperIntegral 0
        (fun y =>
          Real.exp (-c * y ^ 2) / (1 + y ^ 4))| ≤
      Real.sqrt (Real.pi / c) / 2 := by
  have hk :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp (-c * y ^ 2) / (1 + y ^ 4))
        (Ioi (0 : ℝ)) :=
    (integrable_kernelZero hc).integrableOn
  have hg :
      IntegrableOn (fun y : ℝ => Real.exp (-c * y ^ 2))
        (Ioi (0 : ℝ)) :=
    (integrable_exp_neg_mul_sq hc).integrableOn
  rw [improperIntegral_eq_integral_Ioi hk,
    ← integral_gaussian_Ioi c]
  rw [abs_of_nonneg
    (setIntegral_nonneg measurableSet_Ioi
      (fun y _ => div_nonneg (Real.exp_nonneg _) (by positivity)))]
  apply setIntegral_mono_on hk hg measurableSet_Ioi
  intro y _
  have hden : 0 < 1 + y ^ 4 := by positivity
  rw [div_le_iff₀ hden]
  exact le_mul_of_one_le_right (Real.exp_nonneg _)
    (by nlinarith [sq_nonneg (y ^ 2)])

private theorem abs_improperIntegral_kernelTwo_le
    {c : ℝ} (hc : 0 < c) :
    |improperIntegral 0
        (fun y =>
          y ^ 2 * Real.exp (-c * y ^ 2) / (1 + y ^ 4))| ≤
      Real.sqrt (Real.pi / c) / 2 := by
  have hk :
      IntegrableOn
        (fun y : ℝ =>
          y ^ 2 * Real.exp (-c * y ^ 2) / (1 + y ^ 4))
        (Ioi (0 : ℝ)) :=
    (integrable_kernelTwo hc).integrableOn
  have hg :
      IntegrableOn (fun y : ℝ => Real.exp (-c * y ^ 2))
        (Ioi (0 : ℝ)) :=
    (integrable_exp_neg_mul_sq hc).integrableOn
  rw [improperIntegral_eq_integral_Ioi hk,
    ← integral_gaussian_Ioi c]
  rw [abs_of_nonneg
    (setIntegral_nonneg measurableSet_Ioi
      (fun y _ =>
        div_nonneg
          (mul_nonneg (sq_nonneg y) (Real.exp_nonneg _))
          (by positivity)))]
  apply setIntegral_mono_on hk hg measurableSet_Ioi
  intro y _
  have hden : 0 < 1 + y ^ 4 := by positivity
  rw [div_le_iff₀ hden]
  have hy : y ^ 2 ≤ 1 + y ^ 4 := by
    nlinarith [sq_nonneg (y ^ 2 - 1)]
  calc
    y ^ 2 * Real.exp (-c * y ^ 2) ≤
        (1 + y ^ 4) * Real.exp (-c * y ^ 2) :=
      mul_le_mul_of_nonneg_right hy (Real.exp_nonneg _)
    _ = Real.exp (-c * y ^ 2) * (1 + y ^ 4) := by ring

theorem gap1 :
    improperIntegral 0 (fun x => Real.sin (x ^ 2)) =
      (1 / 2 : ℝ) *
        improperIntegral 0 (fun x => Real.sin x / Real.sqrt x) := by
  rw [improperIntegral_fresnel_sin, improperIntegral_weighted_sin]
  linarith [twice_fresnel_value]

theorem gap2 :
    improperIntegral 0 (fun x => Real.cos (x ^ 2)) =
      (1 / 2 : ℝ) *
        improperIntegral 0 (fun x => Real.cos x / Real.sqrt x) := by
  rw [improperIntegral_fresnel_cos, improperIntegral_weighted_cos]
  linarith [twice_fresnel_value]

theorem gap3 (x₀ x₁ : ℝ) (hx₀ : 0 < x₀) (h01 : x₀ ≤ x₁) :
    (∫ x in x₀..x₁, Real.sin x / Real.sqrt x) =
      2 / Real.sqrt Real.pi *
        ∫ x in x₀..x₁,
          improperIntegral 0
            (fun y => Real.sin x * Real.exp (-x * y ^ 2)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le h01] at hx
  have hxpos : 0 < x := hx₀.trans_le hx.1
  change Real.sin x / Real.sqrt x =
    2 / Real.sqrt Real.pi *
      improperIntegral 0 (fun y => Real.sin x * Real.exp (-x * y ^ 2))
  rw [improperIntegral_const_mul_gaussian (Real.sin x) hxpos,
    Real.sqrt_div Real.pi_pos.le]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hxpos).ne'
  field_simp [hp, hs]
  <;> ring

theorem gap4 (x y x₀ : ℝ) (hx : x₀ ≤ x) :
    |Real.sin x * Real.exp (-x * y ^ 2)| ≤
      Real.exp (-x₀ * y ^ 2) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |Real.sin x| * Real.exp (-x * y ^ 2) ≤
        1 * Real.exp (-x * y ^ 2) :=
      mul_le_mul_of_nonneg_right (Real.abs_sin_le_one x)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-x₀ * y ^ 2) := by
      simpa using Real.exp_le_exp.mpr
        (by nlinarith [sq_nonneg y])

theorem gap5 (x₀ x₁ : ℝ) (hx₀ : 0 < x₀) (h01 : x₀ ≤ x₁) :
    (∫ x in x₀..x₁, Real.sin x / Real.sqrt x) =
      2 / Real.sqrt Real.pi *
        improperIntegral 0
          (fun y =>
            ∫ x in x₀..x₁,
              Real.sin x * Real.exp (-x * y ^ 2)) := by
  have hrect :=
    integrable_sin_mul_gaussian_rectangle hx₀ h01
  have houter :
      IntegrableOn
        (fun y : ℝ =>
          ∫ x in x₀..x₁,
            Real.sin x * Real.exp (-x * y ^ 2))
        (Ioi (0 : ℝ)) := by
    change
      Integrable
        (fun y : ℝ =>
          ∫ x in x₀..x₁,
            Real.sin x * Real.exp (-x * y ^ 2))
        (volume.restrict (Ioi (0 : ℝ)))
    simpa only [intervalIntegral.integral_of_le h01,
      uIoc_of_le h01] using hrect.integral_prod_right
  have hleft :
      (∫ x in x₀..x₁,
          improperIntegral 0
            (fun y => Real.sin x * Real.exp (-x * y ^ 2))) =
        ∫ x in x₀..x₁,
          ∫ y in Ioi (0 : ℝ),
            Real.sin x * Real.exp (-x * y ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le h01] at hx
    have hxpos : 0 < x := hx₀.trans_le hx.1
    exact improperIntegral_eq_integral_Ioi
      ((integrable_exp_neg_mul_sq hxpos).const_mul
        (Real.sin x)).integrableOn
  have hswap :
      (∫ x in x₀..x₁,
          ∫ y in Ioi (0 : ℝ),
            Real.sin x * Real.exp (-x * y ^ 2)) =
        ∫ y in Ioi (0 : ℝ),
          ∫ x in x₀..x₁,
            Real.sin x * Real.exp (-x * y ^ 2) := by
    simpa using
      (intervalIntegral_integral_swap
        (μ := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x y : ℝ =>
          Real.sin x * Real.exp (-x * y ^ 2)) hrect)
  calc
    (∫ x in x₀..x₁, Real.sin x / Real.sqrt x) =
        2 / Real.sqrt Real.pi *
          ∫ x in x₀..x₁,
            improperIntegral 0
              (fun y => Real.sin x * Real.exp (-x * y ^ 2)) :=
      gap3 x₀ x₁ hx₀ h01
    _ = 2 / Real.sqrt Real.pi *
        (∫ y in Ioi (0 : ℝ),
          ∫ x in x₀..x₁,
            Real.sin x * Real.exp (-x * y ^ 2)) := by
      rw [hleft, hswap]
    _ = 2 / Real.sqrt Real.pi *
        improperIntegral 0
          (fun y =>
            ∫ x in x₀..x₁,
              Real.sin x * Real.exp (-x * y ^ 2)) := by
      rw [improperIntegral_eq_integral_Ioi houter]

theorem gap6 (x₀ x₁ : ℝ) (hx₀ : 0 < x₀) (h01 : x₀ ≤ x₁) :
    (∫ x in x₀..x₁, Real.sin x / Real.sqrt x) =
        2 / Real.sqrt Real.pi * Real.sin x₀ *
          improperIntegral 0
            (fun y =>
              y ^ 2 * Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) +
        2 / Real.sqrt Real.pi * Real.cos x₀ *
          improperIntegral 0
            (fun y =>
              Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) -
        2 / Real.sqrt Real.pi * Real.sin x₁ *
          improperIntegral 0
            (fun y =>
              y ^ 2 * Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) -
        2 / Real.sqrt Real.pi * Real.cos x₁ *
          improperIntegral 0
            (fun y =>
              Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) := by
  calc
    (∫ x in x₀..x₁, Real.sin x / Real.sqrt x) =
        2 / Real.sqrt Real.pi *
          improperIntegral 0
            (fun y =>
              ∫ x in x₀..x₁,
                Real.sin x * Real.exp (-x * y ^ 2)) :=
      gap5 x₀ x₁ hx₀ h01
    _ = 2 / Real.sqrt Real.pi *
        (Real.sin x₀ *
            improperIntegral 0
              (fun y =>
                y ^ 2 * Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) +
          Real.cos x₀ *
            improperIntegral 0
              (fun y =>
                Real.exp (-x₀ * y ^ 2) / (1 + y ^ 4)) -
          Real.sin x₁ *
            improperIntegral 0
              (fun y =>
                y ^ 2 * Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) -
          Real.cos x₁ *
            improperIntegral 0
              (fun y =>
                Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4))) := by
      rw [improperIntegral_interval_sin_mul_gaussian hx₀ h01]
    _ = _ := by ring

theorem gap7 (x₁ : ℝ) (hx₁ : 0 < x₁) :
    (∫ x in (0 : ℝ)..x₁, Real.sin x / Real.sqrt x) =
        2 / Real.sqrt Real.pi *
          improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) -
        2 / Real.sqrt Real.pi * Real.sin x₁ *
          improperIntegral 0
            (fun y =>
              y ^ 2 * Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) -
        2 / Real.sqrt Real.pi * Real.cos x₁ *
          improperIntegral 0
            (fun y =>
              Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)) := by
  have hweighted :
      IntegrableOn (fun x : ℝ => Real.sin x / Real.sqrt x)
        (Icc (0 : ℝ) x₁) := by
    have hprod :
        IntegrableOn
          (fun x : ℝ => (1 / Real.sqrt x) * Real.sin x)
          (Icc (0 : ℝ) x₁) :=
      (integrableOn_one_div_sqrt_Icc hx₁.le).mul_continuousOn
        Real.continuous_sin.continuousOn isCompact_Icc
    exact hprod.congr_fun
      (fun x _ => by ring) measurableSet_Icc
  have heps_mem :
      ∀ᶠ n : ℕ in atTop, epsilon n ∈ uIcc (0 : ℝ) x₁ := by
    filter_upwards [tendsto_epsilon.eventually_lt_const hx₁] with n hn
    rw [uIcc_of_le hx₁.le]
    exact ⟨(epsilon_pos n).le, hn.le⟩
  have heps_within :
      Tendsto epsilon atTop (𝓝[ uIcc (0 : ℝ) x₁] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_epsilon, heps_mem⟩
  have hleft :
      Tendsto
        (fun n : ℕ =>
          ∫ x in epsilon n..x₁,
            Real.sin x / Real.sqrt x)
        atTop
        (𝓝 (∫ x in (0 : ℝ)..x₁,
          Real.sin x / Real.sqrt x)) := by
    have hweighted' :
        IntegrableOn (fun x : ℝ => Real.sin x / Real.sqrt x)
          (uIcc (0 : ℝ) x₁) := by
      simpa [uIcc_of_le hx₁.le] using hweighted
    exact
      ((intervalIntegral.continuousOn_primitive_interval_left
        hweighted') 0 left_mem_uIcc).tendsto.comp heps_within
  have hfirst :
      Tendsto
        (fun n : ℕ =>
          Real.sin (epsilon n) *
            improperIntegral 0
              (fun y =>
                y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                  (1 + y ^ 4)))
        atTop (𝓝 0) := by
    refine tendsto_sin_kernelTwo_integrals.congr' ?_
    filter_upwards with n
    rw [improperIntegral_eq_integral_Ioi
      (integrable_kernelTwo (epsilon_pos n)).integrableOn,
      integral_const_mul]
  have hcos :
      Tendsto (fun n : ℕ => Real.cos (epsilon n))
        atTop (𝓝 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp
      tendsto_epsilon
  have hsecond :
      Tendsto
        (fun n : ℕ =>
          Real.cos (epsilon n) *
            improperIntegral 0
              (fun y =>
                Real.exp (-epsilon n * y ^ 2) / (1 + y ^ 4)))
        atTop
        (𝓝 (improperIntegral 0
          (fun y => 1 / (1 + y ^ 4)))) := by
    rw [improperIntegral_eq_integral_Ioi
      integrable_quarticKernel.integrableOn]
    have hmul :
        Tendsto
          (fun n : ℕ =>
            Real.cos (epsilon n) *
              (∫ y in Ioi (0 : ℝ),
                Real.exp (-epsilon n * y ^ 2) / (1 + y ^ 4)))
          atTop
          (𝓝 (∫ y in Ioi (0 : ℝ), 1 / (1 + y ^ 4))) := by
      simpa using hcos.mul tendsto_kernelZero_integrals
    refine hmul.congr' ?_
    filter_upwards with n
    rw [improperIntegral_eq_integral_Ioi
      (integrable_kernelZero (epsilon_pos n)).integrableOn]
  have hscaledFirst :
      Tendsto
        (fun n : ℕ =>
          2 / Real.sqrt Real.pi *
            (Real.sin (epsilon n) *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                    (1 + y ^ 4))))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hfirst :
        Tendsto
          (fun n : ℕ =>
            2 / Real.sqrt Real.pi *
              (Real.sin (epsilon n) *
                improperIntegral 0
                  (fun y =>
                    y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                      (1 + y ^ 4))))
          atTop (𝓝 ((2 / Real.sqrt Real.pi) * 0)))
  have hscaledSecond :
      Tendsto
        (fun n : ℕ =>
          2 / Real.sqrt Real.pi *
            (Real.cos (epsilon n) *
              improperIntegral 0
                (fun y =>
                  Real.exp (-epsilon n * y ^ 2) /
                    (1 + y ^ 4))))
        atTop
        (𝓝 (2 / Real.sqrt Real.pi *
          improperIntegral 0
            (fun y => 1 / (1 + y ^ 4)))) :=
    tendsto_const_nhds.mul hsecond
  have htailTwo :
      Tendsto
        (fun _ : ℕ =>
          2 / Real.sqrt Real.pi * Real.sin x₁ *
            improperIntegral 0
              (fun y =>
                y ^ 2 * Real.exp (-x₁ * y ^ 2) /
                  (1 + y ^ 4)))
        atTop
        (𝓝 (2 / Real.sqrt Real.pi * Real.sin x₁ *
          improperIntegral 0
            (fun y =>
              y ^ 2 * Real.exp (-x₁ * y ^ 2) /
                (1 + y ^ 4)))) :=
    tendsto_const_nhds
  have htailZero :
      Tendsto
        (fun _ : ℕ =>
          2 / Real.sqrt Real.pi * Real.cos x₁ *
            improperIntegral 0
              (fun y =>
                Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)))
        atTop
        (𝓝 (2 / Real.sqrt Real.pi * Real.cos x₁ *
          improperIntegral 0
            (fun y =>
              Real.exp (-x₁ * y ^ 2) / (1 + y ^ 4)))) :=
    tendsto_const_nhds
  have hright :
      Tendsto
        (fun n : ℕ =>
          2 / Real.sqrt Real.pi *
              (Real.sin (epsilon n) *
                improperIntegral 0
                  (fun y =>
                    y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                      (1 + y ^ 4))) +
            2 / Real.sqrt Real.pi *
              (Real.cos (epsilon n) *
                improperIntegral 0
                  (fun y =>
                    Real.exp (-epsilon n * y ^ 2) /
                      (1 + y ^ 4))) -
            2 / Real.sqrt Real.pi * Real.sin x₁ *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.cos x₁ *
              improperIntegral 0
                (fun y =>
                  Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)))
        atTop
        (𝓝 (0 +
            2 / Real.sqrt Real.pi *
              improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.sin x₁ *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.cos x₁ *
              improperIntegral 0
                (fun y =>
                  Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)))) :=
    ((hscaledFirst.add hscaledSecond).sub htailTwo).sub htailZero
  have heq :
      ∀ᶠ n : ℕ in atTop,
        (∫ x in epsilon n..x₁,
            Real.sin x / Real.sqrt x) =
          2 / Real.sqrt Real.pi *
              (Real.sin (epsilon n) *
                improperIntegral 0
                  (fun y =>
                    y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                      (1 + y ^ 4))) +
            2 / Real.sqrt Real.pi *
              (Real.cos (epsilon n) *
                improperIntegral 0
                  (fun y =>
                    Real.exp (-epsilon n * y ^ 2) /
                      (1 + y ^ 4))) -
            2 / Real.sqrt Real.pi * Real.sin x₁ *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.cos x₁ *
              improperIntegral 0
                (fun y =>
                  Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)) := by
    filter_upwards [tendsto_epsilon.eventually_lt_const hx₁] with n hn
    calc
      (∫ x in epsilon n..x₁,
          Real.sin x / Real.sqrt x) =
          2 / Real.sqrt Real.pi * Real.sin (epsilon n) *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                    (1 + y ^ 4)) +
            2 / Real.sqrt Real.pi * Real.cos (epsilon n) *
              improperIntegral 0
                (fun y =>
                  Real.exp (-epsilon n * y ^ 2) /
                    (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.sin x₁ *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.cos x₁ *
              improperIntegral 0
                (fun y =>
                  Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)) :=
        gap6 (epsilon n) x₁ (epsilon_pos n) hn.le
      _ = _ := by ring
  have hright' :
      Tendsto
        (fun n : ℕ =>
          2 / Real.sqrt Real.pi *
              (Real.sin (epsilon n) *
                improperIntegral 0
                  (fun y =>
                    y ^ 2 * Real.exp (-epsilon n * y ^ 2) /
                      (1 + y ^ 4))) +
            2 / Real.sqrt Real.pi *
              (Real.cos (epsilon n) *
                improperIntegral 0
                  (fun y =>
                    Real.exp (-epsilon n * y ^ 2) /
                      (1 + y ^ 4))) -
            2 / Real.sqrt Real.pi * Real.sin x₁ *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.cos x₁ *
              improperIntegral 0
                (fun y =>
                  Real.exp (-x₁ * y ^ 2) /
                    (1 + y ^ 4)))
        atTop
        (𝓝 (∫ x in (0 : ℝ)..x₁,
          Real.sin x / Real.sqrt x)) :=
    hleft.congr' heq
  simpa using tendsto_nhds_unique hright' hright

theorem gap8 (x₁ : ℝ) (hx₁ : 0 < x₁) :
    improperIntegral 0 (fun y => Real.exp (-x₁ * y ^ 2)) =
      (1 / 2 : ℝ) * Real.sqrt (Real.pi / x₁) := by
  rw [improperIntegral_eq_of_tendsto (tendsto_gaussian_interval hx₁)]
  ring

theorem gap9 :
    Tendsto (fun x₁ : ℝ => Real.sqrt (Real.pi / x₁))
      atTop (nhds 0) := by
  have hdiv :
      Tendsto (fun x₁ : ℝ => Real.pi / x₁) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop tendsto_id :
        Tendsto (fun x₁ : ℝ => Real.pi / x₁) atTop (𝓝 0))
  simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hdiv

theorem gap10 :
    improperIntegral 0 (fun x => Real.sin x / Real.sqrt x) =
      2 / Real.sqrt Real.pi *
        improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) := by
  have hbound :
      Tendsto
        (fun B : ℝ =>
          |2 / Real.sqrt Real.pi| *
            (Real.sqrt (Real.pi / B) / 2))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul (gap9.div_const 2) :
        Tendsto
          (fun B : ℝ =>
            |2 / Real.sqrt Real.pi| *
              (Real.sqrt (Real.pi / B) / 2))
          atTop (𝓝 (|2 / Real.sqrt Real.pi| * (0 / 2))))
  have hremTwo :
      Tendsto
        (fun B : ℝ =>
          2 / Real.sqrt Real.pi *
            (Real.sin B *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-B * y ^ 2) /
                    (1 + y ^ 4))))
        atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun B : ℝ =>
        |2 / Real.sqrt Real.pi| *
          (Real.sqrt (Real.pi / B) / 2))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc
        |2 / Real.sqrt Real.pi| *
            (|Real.sin B| *
              |improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-B * y ^ 2) /
                    (1 + y ^ 4))|) ≤
          |2 / Real.sqrt Real.pi| *
            (1 *
              |improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-B * y ^ 2) /
                    (1 + y ^ 4))|) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (Real.abs_sin_le_one B) (abs_nonneg _))
              (abs_nonneg _)
        _ ≤ |2 / Real.sqrt Real.pi| *
            (1 * (Real.sqrt (Real.pi / B) / 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (abs_improperIntegral_kernelTwo_le hB) zero_le_one)
            (abs_nonneg _)
        _ = |2 / Real.sqrt Real.pi| *
            (Real.sqrt (Real.pi / B) / 2) := by ring
    · exact hbound
  have hremZero :
      Tendsto
        (fun B : ℝ =>
          2 / Real.sqrt Real.pi *
            (Real.cos B *
              improperIntegral 0
                (fun y =>
                  Real.exp (-B * y ^ 2) / (1 + y ^ 4))))
        atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun B : ℝ =>
        |2 / Real.sqrt Real.pi| *
          (Real.sqrt (Real.pi / B) / 2))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc
        |2 / Real.sqrt Real.pi| *
            (|Real.cos B| *
              |improperIntegral 0
                (fun y =>
                  Real.exp (-B * y ^ 2) /
                    (1 + y ^ 4))|) ≤
          |2 / Real.sqrt Real.pi| *
            (1 *
              |improperIntegral 0
                (fun y =>
                  Real.exp (-B * y ^ 2) /
                    (1 + y ^ 4))|) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (Real.abs_cos_le_one B) (abs_nonneg _))
              (abs_nonneg _)
        _ ≤ |2 / Real.sqrt Real.pi| *
            (1 * (Real.sqrt (Real.pi / B) / 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (abs_improperIntegral_kernelZero_le hB) zero_le_one)
            (abs_nonneg _)
        _ = |2 / Real.sqrt Real.pi| *
            (Real.sqrt (Real.pi / B) / 2) := by ring
    · exact hbound
  have hright :
      Tendsto
        (fun B : ℝ =>
          2 / Real.sqrt Real.pi *
              improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi *
              (Real.sin B *
                improperIntegral 0
                  (fun y =>
                    y ^ 2 * Real.exp (-B * y ^ 2) /
                      (1 + y ^ 4))) -
            2 / Real.sqrt Real.pi *
              (Real.cos B *
                improperIntegral 0
                  (fun y =>
                    Real.exp (-B * y ^ 2) /
                      (1 + y ^ 4))))
        atTop
        (𝓝 (2 / Real.sqrt Real.pi *
          improperIntegral 0
            (fun y => 1 / (1 + y ^ 4)))) := by
    simpa using
      ((tendsto_const_nhds.sub hremTwo).sub hremZero)
  have heq :
      ∀ᶠ B : ℝ in atTop,
        (∫ x in (0 : ℝ)..B,
            Real.sin x / Real.sqrt x) =
          2 / Real.sqrt Real.pi *
              improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi *
              (Real.sin B *
                improperIntegral 0
                  (fun y =>
                    y ^ 2 * Real.exp (-B * y ^ 2) /
                      (1 + y ^ 4))) -
            2 / Real.sqrt Real.pi *
              (Real.cos B *
                improperIntegral 0
                  (fun y =>
                    Real.exp (-B * y ^ 2) /
                      (1 + y ^ 4))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    calc
      (∫ x in (0 : ℝ)..B,
          Real.sin x / Real.sqrt x) =
          2 / Real.sqrt Real.pi *
              improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.sin B *
              improperIntegral 0
                (fun y =>
                  y ^ 2 * Real.exp (-B * y ^ 2) /
                    (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi * Real.cos B *
              improperIntegral 0
                (fun y =>
                  Real.exp (-B * y ^ 2) /
                    (1 + y ^ 4)) :=
        gap7 B hB
      _ = _ := by ring
  have hright' :
      Tendsto
        (fun B : ℝ =>
          2 / Real.sqrt Real.pi *
              improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) -
            2 / Real.sqrt Real.pi *
              (Real.sin B *
                improperIntegral 0
                  (fun y =>
                    y ^ 2 * Real.exp (-B * y ^ 2) /
                      (1 + y ^ 4))) -
            2 / Real.sqrt Real.pi *
              (Real.cos B *
                improperIntegral 0
                  (fun y =>
                    Real.exp (-B * y ^ 2) /
                      (1 + y ^ 4))))
        atTop (𝓝 (Real.sqrt (Real.pi / 2))) :=
    tendsto_weighted_sin.congr' heq
  rw [improperIntegral_weighted_sin]
  exact tendsto_nhds_unique hright' hright

theorem gap11 :
    2 / Real.sqrt Real.pi *
        improperIntegral 0 (fun y => 1 / (1 + y ^ 4)) =
      2 / Real.sqrt Real.pi * (Real.pi / (2 * Real.sqrt 2)) := by
  rw [← gap10, improperIntegral_weighted_sin]
  symm
  rw [← twice_fresnel_value]
  have hp : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hp_sq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  field_simp [hp]
  nlinarith

theorem gap12 :
    2 / Real.sqrt Real.pi * (Real.pi / (2 * Real.sqrt 2)) =
      Real.sqrt (Real.pi / 2) := by
  rw [← twice_fresnel_value]
  have hp : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hp_sq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  field_simp [hp]
  nlinarith

theorem gap13 :
    improperIntegral 0 (fun x => Real.sin x / Real.sqrt x) =
      Real.sqrt (Real.pi / 2) := improperIntegral_weighted_sin

theorem gap14 :
    improperIntegral 0 (fun x => Real.sin (x ^ 2)) =
      (1 / 2 : ℝ) *
        improperIntegral 0 (fun x => Real.sin x / Real.sqrt x) := gap1

theorem gap15 :
    (1 / 2 : ℝ) *
        improperIntegral 0 (fun x => Real.sin x / Real.sqrt x) =
      Real.sqrt Real.pi / (2 * Real.sqrt 2) := by
  rw [improperIntegral_weighted_sin]
  linarith [twice_fresnel_value]

theorem gap16 :
    improperIntegral 0 (fun x => Real.sin (x ^ 2)) =
      Real.sqrt Real.pi / (2 * Real.sqrt 2) := improperIntegral_fresnel_sin

theorem gap17 :
    improperIntegral 0 (fun x => Real.cos (x ^ 2)) =
      Real.sqrt Real.pi / (2 * Real.sqrt 2) := improperIntegral_fresnel_cos

end

end ProofGap.Exercise3830
