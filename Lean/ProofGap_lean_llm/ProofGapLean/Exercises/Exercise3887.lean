import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise3887

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform Interval Topology

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def cutoffSine (x : ℝ) : ℝ :=
  if |x| ≤ Real.pi then Real.sin x else 0

def sineCoefficient (lam : ℝ) : ℝ :=
  2 / Real.pi * improperIntegral 0
    (fun ξ => cutoffSine ξ * Real.sin (lam * ξ))

private theorem improperIntegral_eq_of_hasImproperIntegral
    {a : ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hL : HasImproperIntegral a f L) :
    improperIntegral a f = L := by
  unfold improperIntegral
  have hs : {y : ℝ | HasImproperIntegral a f y} = {L} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hy
      exact tendsto_nhds_unique hy hL
    · rintro rfl
      exact hL
  rw [hs]
  exact csInf_singleton L

private theorem hasDerivAt_sin_linear_div (c x : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.sin (c * t) / c) (Real.cos (c * x)) x := by
  convert (((Real.hasDerivAt_sin (c * x)).comp x
    ((hasDerivAt_const x c).mul (hasDerivAt_id x))).div_const c) using 1 <;>
    field_simp [hc] <;> ring

theorem gap1 :
    Continuous cutoffSine := by
  unfold cutoffSine
  refine
    Real.continuous_sin.if_le continuous_const
      continuous_id.abs continuous_const ?_
  intro x hx
  by_cases hx0 : 0 ≤ x
  · have hxeq : x = Real.pi := by
      simpa [abs_of_nonneg hx0] using hx
    rw [hxeq, Real.sin_pi]
  · have hx0' : x ≤ 0 := le_of_not_ge hx0
    rw [abs_of_nonpos hx0'] at hx
    have hxeq : x = -Real.pi := by linarith
    rw [hxeq, Real.sin_neg, Real.sin_pi, neg_zero]

theorem gap2 :
    Function.Odd cutoffSine := by
  intro x
  by_cases hx : |x| ≤ Real.pi <;>
    simp [cutoffSine, abs_neg, Real.sin_neg, hx]

theorem gap3 (lam : ℝ) :
    sineCoefficient lam =
      2 / Real.pi * improperIntegral 0
        (fun ξ => cutoffSine ξ * Real.sin (lam * ξ)) := by
  rfl

theorem gap4 (lam : ℝ) :
    2 / Real.pi * improperIntegral 0
        (fun ξ => cutoffSine ξ * Real.sin (lam * ξ)) =
      2 / Real.pi *
        ∫ ξ in (0 : ℝ)..Real.pi, Real.sin ξ * Real.sin (lam * ξ) := by
  congr 1
  apply improperIntegral_eq_of_hasImproperIntegral
  unfold HasImproperIntegral
  let f : ℝ → ℝ := fun ξ =>
    cutoffSine ξ * Real.sin (lam * ξ)
  have hf : Continuous f := by
    dsimp [f]
    exact gap1.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop Real.pi] with b hb
  have hzero : (∫ ξ in Real.pi..b, f ξ) = 0 := by
    calc
      (∫ ξ in Real.pi..b, f ξ) = ∫ ξ in Real.pi..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro ξ hξ
        rw [Set.uIcc_of_le hb] at hξ
        dsimp [f]
        have hξ0 : 0 ≤ ξ := Real.pi_pos.le.trans hξ.1
        by_cases hξpi : ξ ≤ Real.pi
        · have heq : ξ = Real.pi := le_antisymm hξpi hξ.1
          subst ξ
          simp [cutoffSine]
        · have hout : ¬|ξ| ≤ Real.pi := by
            rw [abs_of_nonneg hξ0]
            exact hξpi
          simp [cutoffSine, hout]
      _ = 0 := by simp
  calc
    (∫ ξ in (0 : ℝ)..b, f ξ) =
        (∫ ξ in (0 : ℝ)..Real.pi, f ξ) +
          ∫ ξ in Real.pi..b, f ξ := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 Real.pi)
        (hf.intervalIntegrable Real.pi b)
    _ = ∫ ξ in (0 : ℝ)..Real.pi, f ξ := by rw [hzero, add_zero]
    _ = ∫ ξ in (0 : ℝ)..Real.pi,
        Real.sin ξ * Real.sin (lam * ξ) := by
      apply intervalIntegral.integral_congr
      intro ξ hξ
      rw [Set.uIcc_of_le Real.pi_pos.le] at hξ
      dsimp [f]
      simp [cutoffSine, abs_of_nonneg hξ.1, hξ.2]

theorem gap5 (lam : ℝ) (hlam : lam ^ 2 ≠ 1) :
    2 / Real.pi *
        ∫ ξ in (0 : ℝ)..Real.pi, Real.sin ξ * Real.sin (lam * ξ) =
      2 * Real.sin (lam * Real.pi) /
        (Real.pi * (1 - lam ^ 2)) := by
  have hm : 1 - lam ≠ 0 := by
    intro hz
    apply hlam
    have : lam = 1 := by linarith
    simp [this]
  have hp : 1 + lam ≠ 0 := by
    intro hz
    apply hlam
    have : lam = -1 := by linarith
    simp [this]
  have hs : 1 - lam ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam)
  let F : ℝ → ℝ := fun x =>
    (Real.sin ((1 - lam) * x) / (1 - lam) -
      Real.sin ((1 + lam) * x) / (1 + lam)) / 2
  have hd (x : ℝ) :
      HasDerivAt F (Real.sin x * Real.sin (lam * x)) x := by
    have h1 := hasDerivAt_sin_linear_div (1 - lam) x hm
    have h2 := hasDerivAt_sin_linear_div (1 + lam) x hp
    dsimp [F]
    convert (h1.sub h2).div_const 2 using 1
    rw [show (1 - lam) * x = x - lam * x by ring,
      show (1 + lam) * x = x + lam * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hInt :
      (∫ x in (0 : ℝ)..Real.pi,
        Real.sin x * Real.sin (lam * x)) = F Real.pi - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hd x
    · exact (Real.continuous_sin.mul
          (Real.continuous_sin.comp
            (continuous_const.mul continuous_id))).intervalIntegrable 0 Real.pi
  have hminus :
      Real.sin ((1 - lam) * Real.pi) =
        Real.sin (lam * Real.pi) := by
    rw [show (1 - lam) * Real.pi =
      Real.pi - lam * Real.pi by ring, Real.sin_sub, Real.sin_pi,
      Real.cos_pi]
    ring
  have hplus :
      Real.sin ((1 + lam) * Real.pi) =
        -Real.sin (lam * Real.pi) := by
    rw [show (1 + lam) * Real.pi =
      Real.pi + lam * Real.pi by ring, Real.sin_add, Real.sin_pi,
      Real.cos_pi]
    ring
  rw [hInt]
  dsimp [F]
  simp only [mul_zero, Real.sin_zero, zero_div, sub_zero]
  rw [hminus, hplus]
  field_simp [hm, hp, hs, Real.pi_ne_zero] <;> ring

theorem gap6 (lam : ℝ) (hlam : lam ^ 2 ≠ 1) :
    sineCoefficient lam =
      2 * Real.sin (lam * Real.pi) /
        (Real.pi * (1 - lam ^ 2)) := by
  exact (gap3 lam).trans ((gap4 lam).trans (gap5 lam hlam))

private theorem sineRatio_abs_le_pi (x : ℝ) :
    |Real.sin (Real.pi * x) / (1 - x ^ 2)| ≤ Real.pi := by
  by_cases hx : 0 ≤ x
  · by_cases hx1 : x = 1
    · simp [hx1, Real.pi_pos.le]
    have harg : Real.pi * (x - 1) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hx1)
    have hsin :
        Real.sin (Real.pi * x) =
          -Real.sin (Real.pi * (x - 1)) := by
      rw [show Real.pi * x = Real.pi * (x - 1) + Real.pi by ring,
        Real.sin_add, Real.sin_pi, Real.cos_pi]
      ring
    have hsq : 1 - x ^ 2 ≠ 0 := by
      intro hz
      have : x ^ 2 = 1 := by linarith
      apply hx1
      nlinarith [sq_nonneg (x - 1)]
    have heq :
        Real.sin (Real.pi * x) / (1 - x ^ 2) =
          Real.pi * Real.sinc (Real.pi * (x - 1)) / (x + 1) := by
      rw [hsin]
      simp only [Real.sinc, if_neg harg]
      field_simp [Real.pi_ne_zero, sub_ne_zero.mpr hx1, hsq]
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by linarith : 0 < x + 1)]
    have hs := Real.abs_sinc_le_one (Real.pi * (x - 1))
    have hden : 0 < x + 1 := by linarith
    apply (div_le_iff₀ hden).2
    nlinarith [Real.pi_pos]
  · have hxle : x ≤ 0 := le_of_not_ge hx
    by_cases hxm1 : x = -1
    · simp [hxm1, Real.pi_pos.le]
    have hxplus : x + 1 ≠ 0 := by
      intro hz
      apply hxm1
      linarith
    have hxminus : 1 - x ≠ 0 := by linarith
    have harg : Real.pi * (x + 1) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero hxplus
    have hsin :
        Real.sin (Real.pi * x) =
          -Real.sin (Real.pi * (x + 1)) := by
      rw [show Real.pi * x = Real.pi * (x + 1) - Real.pi by ring,
        Real.sin_sub, Real.sin_pi, Real.cos_pi]
      ring
    have hsq : 1 - x ^ 2 ≠ 0 := by
      intro hz
      have : x ^ 2 = 1 := by linarith
      apply hxm1
      nlinarith [sq_nonneg (x + 1)]
    have heq :
        Real.sin (Real.pi * x) / (1 - x ^ 2) =
          -(Real.pi * Real.sinc (Real.pi * (x + 1)) / (1 - x)) := by
      rw [hsin]
      simp only [Real.sinc, if_neg harg]
      field_simp [Real.pi_ne_zero, hxplus, hxminus, hsq]
      ring
    rw [heq, abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by linarith : 0 < 1 - x)]
    have hs := Real.abs_sinc_le_one (Real.pi * (x + 1))
    have hden : 0 < 1 - x := by linarith
    apply (div_le_iff₀ hden).2
    nlinarith [Real.pi_pos]

private theorem sineRatio_integrable :
    Integrable
      (fun x : ℝ => Real.sin (Real.pi * x) / (1 - x ^ 2)) := by
  let g : ℝ → ℝ := fun x =>
    (5 * Real.pi + 2) * (1 + x ^ 2)⁻¹
  have hg : Integrable g :=
    integrable_inv_one_add_sq.const_mul (5 * Real.pi + 2)
  refine hg.mono' (by
    exact
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).div
        (measurable_const.sub
          (measurable_id.pow_const 2))).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  dsimp [g]
  have hden : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : |x| ≤ 2
  · have hx_sq : x ^ 2 ≤ 4 := by
      nlinarith [sq_abs x, sq_nonneg (2 - |x|), abs_nonneg x]
    calc
      |Real.sin (Real.pi * x) / (1 - x ^ 2)| ≤ Real.pi :=
        sineRatio_abs_le_pi x
      _ ≤ (5 * Real.pi + 2) * (1 + x ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (le_div_iff₀ hden).2
        nlinarith [Real.pi_pos]
  · have habs : 2 < |x| := lt_of_not_ge hx
    have hx_sq : 4 < x ^ 2 := by
      rw [← sq_abs x]
      nlinarith
    have hden2 : 0 < x ^ 2 - 1 := by linarith
    have habsden : |1 - x ^ 2| = x ^ 2 - 1 := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    have hsin : |Real.sin (Real.pi * x)| ≤ 1 :=
      Real.abs_sin_le_one _
    rw [abs_div, habsden]
    calc
      |Real.sin (Real.pi * x)| / (x ^ 2 - 1) ≤
          1 / (x ^ 2 - 1) :=
        (div_le_div_iff_of_pos_right hden2).2 hsin
      _ ≤ 2 / (1 + x ^ 2) := by
        apply (div_le_div_iff₀ hden2 hden).2
        linarith
      _ ≤ (5 * Real.pi + 2) * (1 + x ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith [Real.pi_pos]

private theorem cutoffSine_hasCompactSupport :
    HasCompactSupport cutoffSine := by
  refine
    HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (-Real.pi) Real.pi)) ?_
  intro x hx
  have hout : ¬|x| ≤ Real.pi := by
    intro hxa
    exact hx ⟨neg_le_of_abs_le hxa, le_of_abs_le hxa⟩
  simp [cutoffSine, hout]

private theorem cutoffSine_integrable :
    Integrable cutoffSine :=
  gap1.integrable_of_hasCompactSupport cutoffSine_hasCompactSupport

private theorem cutoffSine_sin_integrable (k : ℝ) :
    Integrable (fun t : ℝ => cutoffSine t * Real.sin (k * t)) := by
  apply cutoffSine_integrable.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (k * t)

private theorem half_sine_integral
    (k : ℝ) (hk : k ^ 2 ≠ 1) :
    (∫ t in Set.Ioi (0 : ℝ),
        cutoffSine t * Real.sin (k * t)) =
      Real.sin (Real.pi * k) / (1 - k ^ 2) := by
  let f : ℝ → ℝ := fun t =>
    cutoffSine t * Real.sin (k * t)
  have hf : Integrable f := cutoffSine_sin_integrable k
  have himproper :
      improperIntegral 0 f = ∫ t in Set.Ioi (0 : ℝ), f t := by
    apply improperIntegral_eq_of_hasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
  have heq := (gap4 k).trans (gap5 k hk)
  change
    2 / Real.pi * improperIntegral 0 f =
      2 * Real.sin (k * Real.pi) /
        (Real.pi * (1 - k ^ 2)) at heq
  rw [himproper] at heq
  rw [mul_comm k Real.pi] at heq
  change
    (∫ t in Set.Ioi (0 : ℝ), f t) =
      Real.sin (Real.pi * k) / (1 - k ^ 2)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : 1 - k ^ 2 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hk)
  field_simp [hpi, hden] at heq ⊢
  linarith

private theorem full_sine_integral
    (k : ℝ) (hk : k ^ 2 ≠ 1) :
    (∫ t : ℝ, cutoffSine t * Real.sin (k * t)) =
      2 * (Real.sin (Real.pi * k) / (1 - k ^ 2)) := by
  let r : ℝ → ℝ := fun t =>
    cutoffSine t * Real.sin (k * t)
  have hr : Integrable r := cutoffSine_sin_integrable k
  have hge (t : ℝ) : r (-t) = r t := by
    dsimp [r]
    rw [gap2 t]
    rw [show k * -t = -(k * t) by ring, Real.sin_neg]
    ring
  have habs (t : ℝ) : r |t| = r t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), hge]
  calc
    (∫ t : ℝ, cutoffSine t * Real.sin (k * t)) =
        ∫ t : ℝ, r t := by rfl
    _ = ∫ t : ℝ, r |t| := by
      apply integral_congr_ae
      filter_upwards with t
      exact (habs t).symm
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), r t :=
      integral_comp_abs
    _ = 2 * (Real.sin (Real.pi * k) / (1 - k ^ 2)) := by
      rw [half_sine_integral k hk]

private theorem integral_cosine_zero (k : ℝ) :
    (∫ t : ℝ, cutoffSine t * Real.cos (k * t)) = 0 := by
  let r : ℝ → ℝ := fun t =>
    cutoffSine t * Real.cos (k * t)
  have hr : Integrable r := by
    apply cutoffSine_integrable.mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (k * t)
  have hneg := integral_neg_eq_self r volume
  have hpoint (t : ℝ) : r (-t) = -r t := by
    dsimp [r]
    rw [gap2 t]
    rw [show k * -t = -(k * t) by ring, Real.cos_neg]
    ring
  simp_rw [hpoint, integral_neg] at hneg
  change (∫ t : ℝ, r t) = 0
  linarith

private def cf (x : ℝ) : ℂ :=
  (cutoffSine x : ℝ)

private theorem cf_integrable :
    Integrable cf :=
  cutoffSine_integrable.ofReal

private theorem cf_fourier
    (w : ℝ) (hw : (2 * Real.pi * w) ^ 2 ≠ 1) :
    𝓕 cf w =
      -((2 * (Real.sin (Real.pi * (2 * Real.pi * w)) /
        (1 - (2 * Real.pi * w) ^ 2)) : ℝ) : ℂ) * Complex.I := by
  let q : ℝ :=
    2 * (Real.sin (Real.pi * (2 * Real.pi * w)) /
      (1 - (2 * Real.pi * w) ^ 2))
  change 𝓕 cf w = -(q : ℂ) * Complex.I
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let J : ℝ → ℂ := fun t =>
    Complex.exp ((-2 * Real.pi * t * w : ℝ) * Complex.I) * cf t
  change (∫ t : ℝ, J t) = _
  have hJ : Integrable J := by
    apply cf_integrable.bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      rw [Complex.norm_exp]
      simp
  have hre := integral_re hJ
  have him := integral_im hJ
  change (∫ t : ℝ, (J t).re) = (∫ t : ℝ, J t).re at hre
  change (∫ t : ℝ, (J t).im) = (∫ t : ℝ, J t).im at him
  have hrePoint (t : ℝ) :
      (J t).re =
        cutoffSine t * Real.cos ((2 * Real.pi * w) * t) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  have himPoint (t : ℝ) :
      (J t).im =
        -(cutoffSine t * Real.sin ((2 * Real.pi * w) * t)) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  simp_rw [hrePoint, integral_cosine_zero (2 * Real.pi * w)] at hre
  simp_rw [himPoint, integral_neg,
    full_sine_integral (2 * Real.pi * w) hw] at him
  have hqre : (-((q : ℝ) : ℂ)).re = -q := by
    norm_cast
  have hqim : (-((q : ℝ) : ℂ)).im = 0 := by
    norm_cast
  apply Complex.ext
  · rw [Complex.mul_re, hqre, hqim]
    norm_num
    exact hre.symm
  · rw [Complex.mul_im, hqre, hqim]
    norm_num
    dsimp [q]
    exact him.symm

private theorem frequency_nonresonant_ae :
    ∀ᵐ w : ℝ, (2 * Real.pi * w) ^ 2 ≠ 1 := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  filter_upwards
    [volume.ae_ne (1 / c), volume.ae_ne (-1 / c)] with w hw₁ hw₂
  intro hsq
  have hfac : (c * w - 1) * (c * w + 1) = 0 := by
    dsimp [c] at hsq ⊢
    nlinarith
  rcases mul_eq_zero.mp hfac with hminus | hplus
  · apply hw₁
    field_simp [hc]
    nlinarith
  · apply hw₂
    field_simp [hc]
    nlinarith

private theorem cf_fourier_integrable :
    Integrable (𝓕 cf) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  let q : ℝ → ℝ := fun z =>
    Real.sin (Real.pi * z) / (1 - z ^ 2)
  have hq : Integrable q := sineRatio_integrable
  have hscaled : Integrable (fun w : ℝ => q (c * w)) :=
    hq.comp_mul_left' hc
  have hreal : Integrable (fun w : ℝ => -(2 * q (c * w))) :=
    (hscaled.const_mul 2).neg
  have hcomplex :
      Integrable (fun w : ℝ => ((-(2 * q (c * w)) : ℝ) : ℂ) * Complex.I) :=
    hreal.ofReal.mul_const Complex.I
  apply hcomplex.congr
  filter_upwards [frequency_nonresonant_ae] with w hw
  dsimp [q, c]
  have hcast :
      ((-(2 * (Real.sin (Real.pi * (2 * Real.pi * w)) /
        (1 - (2 * Real.pi * w) ^ 2))) : ℝ) : ℂ) =
        -((2 * (Real.sin (Real.pi * (2 * Real.pi * w)) /
          (1 - (2 * Real.pi * w) ^ 2)) : ℝ) : ℂ) := by
    norm_cast
  rw [hcast]
  exact (cf_fourier w hw).symm

private theorem fourier_full_real (x : ℝ) :
    (∫ w : ℝ,
        2 * (Real.sin (Real.pi * (2 * Real.pi * w)) /
          (1 - (2 * Real.pi * w) ^ 2)) *
          Real.sin (2 * Real.pi * w * x)) =
      cutoffSine x := by
  have hinv :=
    cf_integrable.fourierInv_fourier_eq cf_fourier_integrable
      (v := x) (by
        unfold cf
        exact (Complex.continuous_ofReal.comp gap1).continuousAt)
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 cf w
  have hinvK : (∫ w : ℝ, K w) = cf x := by
    rw [Real.fourierInv_eq'] at hinv
    have hinner (v : ℝ) : inner ℝ v x = v * x := by
      change x * v = v * x
      ring
    simp_rw [hinner] at hinv
    simpa [K, smul_eq_mul, RCLike.inner_apply, mul_comm, mul_left_comm,
      mul_assoc] using hinv
  have hK : Integrable K := by
    apply cf_fourier_integrable.bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with w
      rw [Complex.norm_exp]
      simp
  have hre := integral_re hK
  change (∫ w : ℝ, (K w).re) = (∫ w : ℝ, K w).re at hre
  have hreval := congrArg Complex.re hinvK
  have htotal := hre.trans hreval
  have hpoint :
      ∀ᵐ w : ℝ,
        (K w).re =
          2 * (Real.sin (Real.pi * (2 * Real.pi * w)) /
            (1 - (2 * Real.pi * w) ^ 2)) *
            Real.sin (2 * Real.pi * w * x) := by
    filter_upwards [frequency_nonresonant_ae] with w hw
    let q : ℝ :=
      2 * (Real.sin (Real.pi * (2 * Real.pi * w)) /
        (1 - (2 * Real.pi * w) ^ 2))
    have hqre : (-((q : ℝ) : ℂ)).re = -q := by
      norm_cast
    have hqim : (-((q : ℝ) : ℂ)).im = 0 := by
      norm_cast
    have hFre : (-((q : ℝ) : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, hqre, hqim]
      norm_num
    have hFim : (-((q : ℝ) : ℂ) * Complex.I).im = -q := by
      rw [Complex.mul_im, hqre, hqim]
      norm_num
    dsimp [K]
    rw [cf_fourier w hw]
    change
      (Complex.exp
        (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
          (-((q : ℝ) : ℂ) * Complex.I)).re = _
    rw [Complex.mul_re, hFre, hFim, Complex.exp_re, Complex.exp_im]
    dsimp [q]
    simp
    ring
  rw [integral_congr_ae hpoint] at htotal
  have hcfre : (cf x).re = cutoffSine x := by
    change (((cutoffSine x : ℝ) : ℂ)).re = cutoffSine x
    norm_cast
  rw [hcfre] at htotal
  exact htotal

private theorem sineKernel_integrable (x : ℝ) :
    Integrable
      (fun lam : ℝ =>
        Real.sin (lam * Real.pi) / (1 - lam ^ 2) *
          Real.sin (lam * x)) := by
  have hratio :
      Integrable
        (fun lam : ℝ =>
          Real.sin (lam * Real.pi) / (1 - lam ^ 2)) := by
    apply sineRatio_integrable.congr
    filter_upwards with lam
    rw [mul_comm lam Real.pi]
  apply hratio.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with lam
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (lam * x)

private theorem inverse_sine_half (x : ℝ) :
    cutoffSine x =
      2 / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          Real.sin (lam * Real.pi) / (1 - lam ^ 2) *
            Real.sin (lam * x) := by
  let g : ℝ → ℝ := fun lam =>
    Real.sin (lam * Real.pi) / (1 - lam ^ 2) *
      Real.sin (lam * x)
  have hg : Integrable g := sineKernel_integrable x
  have hge (lam : ℝ) : g (-lam) = g lam := by
    dsimp [g]
    rw [show -lam * Real.pi = -(lam * Real.pi) by ring,
      show -lam * x = -(lam * x) by ring,
      Real.sin_neg, Real.sin_neg]
    ring
  have habs (lam : ℝ) : g |lam| = g lam := by
    by_cases hlam : 0 ≤ lam
    · rw [abs_of_nonneg hlam]
    · rw [abs_of_neg (lt_of_not_ge hlam), hge]
  have heven :
      (∫ lam : ℝ, g lam) =
        2 * ∫ lam in Set.Ioi (0 : ℝ), g lam := by
    calc
      (∫ lam : ℝ, g lam) =
          ∫ lam : ℝ, g |lam| := by
        apply integral_congr_ae
        filter_upwards with lam
        exact (habs lam).symm
      _ = 2 * ∫ lam in Set.Ioi (0 : ℝ), g lam :=
        integral_comp_abs
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hscale :
      (∫ w : ℝ, 2 * g (c * w)) =
        1 / Real.pi * ∫ lam : ℝ, g lam := by
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.2 hc)]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  have hfull :
      (∫ w : ℝ, 2 * g (c * w)) = cutoffSine x := by
    rw [← fourier_full_real x]
    apply integral_congr_ae
    filter_upwards with w
    dsimp [g, c]
    ring
  have hmain :
      1 / Real.pi *
          (2 * ∫ lam in Set.Ioi (0 : ℝ), g lam) =
        cutoffSine x := by
    rw [← heven]
    exact hscale.symm.trans hfull
  change cutoffSine x =
    2 / Real.pi * ∫ lam in Set.Ioi (0 : ℝ), g lam
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hmain ⊢
  linarith

theorem gap7 (x : ℝ) :
    cutoffSine x =
      2 / Real.pi * improperIntegral 0
        (fun lam =>
          Real.sin (lam * Real.pi) / (1 - lam ^ 2) *
            Real.sin (lam * x)) := by
  let g : ℝ → ℝ := fun lam =>
    Real.sin (lam * Real.pi) / (1 - lam ^ 2) *
      Real.sin (lam * x)
  have hg : Integrable g := sineKernel_integrable x
  have himproper :
      improperIntegral 0 g =
        ∫ lam in Set.Ioi (0 : ℝ), g lam := by
    apply improperIntegral_eq_of_hasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi 0 hg.integrableOn tendsto_id
  change cutoffSine x = 2 / Real.pi * improperIntegral 0 g
  rw [himproper]
  exact inverse_sine_half x

end

end ProofGap.Exercise3887
