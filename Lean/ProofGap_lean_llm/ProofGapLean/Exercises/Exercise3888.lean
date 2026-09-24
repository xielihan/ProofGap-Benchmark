import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise3888

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform Interval Topology

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def cutoffCosine (x : ℝ) : ℝ :=
  if |x| ≤ Real.pi / 2 then Real.cos x else 0

def cosineCoefficient (lam : ℝ) : ℝ :=
  2 / Real.pi * improperIntegral 0
    (fun ξ => cutoffCosine ξ * Real.cos (lam * ξ))

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
    Continuous cutoffCosine := by
  unfold cutoffCosine
  refine
    Real.continuous_cos.if_le continuous_const
      continuous_id.abs continuous_const ?_
  intro x hx
  by_cases hx0 : 0 ≤ x
  · have hxeq : x = Real.pi / 2 := by
      simpa [abs_of_nonneg hx0] using hx
    rw [hxeq, Real.cos_pi_div_two]
  · have hx0' : x ≤ 0 := le_of_not_ge hx0
    rw [abs_of_nonpos hx0'] at hx
    have hxeq : x = -(Real.pi / 2) := by linarith
    rw [hxeq, Real.cos_neg, Real.cos_pi_div_two]

theorem gap2 :
    Function.Even cutoffCosine := by
  intro x
  by_cases hx : |x| ≤ Real.pi / 2 <;>
    simp [cutoffCosine, abs_neg, Real.cos_neg, hx]

theorem gap3 (lam : ℝ) :
    cosineCoefficient lam =
      2 / Real.pi * improperIntegral 0
        (fun ξ => cutoffCosine ξ * Real.cos (lam * ξ)) := by
  rfl

theorem gap4 (lam : ℝ) :
    2 / Real.pi * improperIntegral 0
        (fun ξ => cutoffCosine ξ * Real.cos (lam * ξ)) =
      2 / Real.pi *
        ∫ ξ in (0 : ℝ)..Real.pi / 2, Real.cos ξ * Real.cos (lam * ξ) := by
  congr 1
  apply improperIntegral_eq_of_hasImproperIntegral
  unfold HasImproperIntegral
  let A : ℝ := Real.pi / 2
  let f : ℝ → ℝ := fun ξ =>
    cutoffCosine ξ * Real.cos (lam * ξ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hf : Continuous f := by
    dsimp [f]
    exact gap1.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [eventually_ge_atTop A] with b hb
  have hzero : (∫ ξ in A..b, f ξ) = 0 := by
    calc
      (∫ ξ in A..b, f ξ) = ∫ ξ in A..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro ξ hξ
        rw [Set.uIcc_of_le hb] at hξ
        dsimp [f]
        have hξ0 : 0 ≤ ξ := hA.trans hξ.1
        by_cases hξA : ξ ≤ A
        · have heq : ξ = A := le_antisymm hξA hξ.1
          subst ξ
          simp [cutoffCosine, A, abs_of_nonneg hA,
            Real.cos_pi_div_two]
        · have hout : ¬|ξ| ≤ Real.pi / 2 := by
            rw [abs_of_nonneg hξ0]
            dsimp [A] at hξA
            exact hξA
          simp [cutoffCosine, hout]
      _ = 0 := by simp
  calc
    (∫ ξ in (0 : ℝ)..b, f ξ) =
        (∫ ξ in (0 : ℝ)..A, f ξ) + ∫ ξ in A..b, f ξ := by
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 A) (hf.intervalIntegrable A b)
    _ = ∫ ξ in (0 : ℝ)..A, f ξ := by rw [hzero, add_zero]
    _ = ∫ ξ in (0 : ℝ)..A,
        Real.cos ξ * Real.cos (lam * ξ) := by
      apply intervalIntegral.integral_congr
      intro ξ hξ
      rw [Set.uIcc_of_le hA] at hξ
      dsimp [f]
      have hinside : |ξ| ≤ Real.pi / 2 := by
        rw [abs_of_nonneg hξ.1]
        simpa [A] using hξ.2
      simp [cutoffCosine, hinside]
    _ = ∫ ξ in (0 : ℝ)..Real.pi / 2,
        Real.cos ξ * Real.cos (lam * ξ) := by rfl

theorem gap5 (lam : ℝ) (hlam : lam ^ 2 ≠ 1) :
    2 / Real.pi *
        ∫ ξ in (0 : ℝ)..Real.pi / 2, Real.cos ξ * Real.cos (lam * ξ) =
      2 * Real.cos (lam * Real.pi / 2) /
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
  let A : ℝ := Real.pi / 2
  let F : ℝ → ℝ := fun x =>
    (Real.sin ((1 - lam) * x) / (1 - lam) +
      Real.sin ((1 + lam) * x) / (1 + lam)) / 2
  have hd (x : ℝ) :
      HasDerivAt F (Real.cos x * Real.cos (lam * x)) x := by
    have h1 := hasDerivAt_sin_linear_div (1 - lam) x hm
    have h2 := hasDerivAt_sin_linear_div (1 + lam) x hp
    dsimp [F]
    convert (h1.add h2).div_const 2 using 1
    rw [show (1 - lam) * x = x - lam * x by ring,
      show (1 + lam) * x = x + lam * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hInt :
      (∫ x in (0 : ℝ)..A,
        Real.cos x * Real.cos (lam * x)) = F A - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hd x
    · exact (Real.continuous_cos.mul
          (Real.continuous_cos.comp
            (continuous_const.mul continuous_id))).intervalIntegrable 0 A
  have hminus :
      Real.sin ((1 - lam) * A) = Real.cos (lam * A) := by
    dsimp [A]
    rw [show (1 - lam) * (Real.pi / 2) =
      Real.pi / 2 - lam * (Real.pi / 2) by ring,
      Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hplus :
      Real.sin ((1 + lam) * A) = Real.cos (lam * A) := by
    dsimp [A]
    rw [show (1 + lam) * (Real.pi / 2) =
      Real.pi / 2 + lam * (Real.pi / 2) by ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hcos :
      Real.cos (lam * A) =
        Real.cos (lam * Real.pi / 2) := by
    congr 1
    dsimp [A]
    ring
  rw [show Real.pi / 2 = A by rfl, hInt]
  dsimp [F]
  simp only [mul_zero, Real.sin_zero, zero_div, add_zero, sub_zero]
  rw [hminus, hplus, hcos]
  field_simp [hm, hp, hs, Real.pi_ne_zero] <;> ring

theorem gap6 (lam : ℝ) (hlam : lam ^ 2 ≠ 1) :
    cosineCoefficient lam =
      2 * Real.cos (lam * Real.pi / 2) /
        (Real.pi * (1 - lam ^ 2)) := by
  exact (gap3 lam).trans ((gap4 lam).trans (gap5 lam hlam))

private theorem cosineRatio_abs_le (x : ℝ) :
    |Real.cos (Real.pi * x / 2) / (1 - x ^ 2)| ≤ Real.pi / 2 := by
  by_cases hx : 0 ≤ x
  · by_cases hx1 : x = 1
    · simp [hx1]
      positivity
    have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have harg : Real.pi * (x - 1) / 2 ≠ 0 := by
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hxsub) (by norm_num)
    have hcos :
        Real.cos (Real.pi * x / 2) =
          -Real.sin (Real.pi * (x - 1) / 2) := by
      rw [show Real.pi * x / 2 =
        Real.pi / 2 + Real.pi * (x - 1) / 2 by ring,
        Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hsq : 1 - x ^ 2 ≠ 0 := by
      intro hz
      have : x ^ 2 = 1 := by linarith
      apply hx1
      nlinarith [sq_nonneg (x - 1)]
    have heq :
        Real.cos (Real.pi * x / 2) / (1 - x ^ 2) =
          (Real.pi / 2) * Real.sinc (Real.pi * (x - 1) / 2) /
            (x + 1) := by
      rw [hcos]
      simp only [Real.sinc, if_neg harg]
      field_simp [Real.pi_ne_zero, hxsub, hsq]
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos (div_pos Real.pi_pos (by norm_num)),
      abs_of_pos (by linarith : 0 < x + 1)]
    have hs := Real.abs_sinc_le_one (Real.pi * (x - 1) / 2)
    have hden : 0 < x + 1 := by linarith
    apply (div_le_iff₀ hden).2
    nlinarith [Real.pi_pos]
  · have hxle : x ≤ 0 := le_of_not_ge hx
    by_cases hxm1 : x = -1
    · simp [hxm1]
      positivity
    have hxplus : x + 1 ≠ 0 := by
      intro hz
      apply hxm1
      linarith
    have hxminus : 1 - x ≠ 0 := by linarith
    have harg : Real.pi * (x + 1) / 2 ≠ 0 := by
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hxplus) (by norm_num)
    have hcos :
        Real.cos (Real.pi * x / 2) =
          Real.sin (Real.pi * (x + 1) / 2) := by
      rw [show Real.pi * x / 2 =
        -(Real.pi / 2) + Real.pi * (x + 1) / 2 by ring,
        Real.cos_add, Real.cos_neg, Real.cos_pi_div_two,
        Real.sin_neg, Real.sin_pi_div_two]
      ring
    have hsq : 1 - x ^ 2 ≠ 0 := by
      intro hz
      have : x ^ 2 = 1 := by linarith
      apply hxm1
      nlinarith [sq_nonneg (x + 1)]
    have heq :
        Real.cos (Real.pi * x / 2) / (1 - x ^ 2) =
          (Real.pi / 2) * Real.sinc (Real.pi * (x + 1) / 2) /
            (1 - x) := by
      rw [hcos]
      simp only [Real.sinc, if_neg harg]
      field_simp [Real.pi_ne_zero, hxplus, hxminus, hsq]
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos (div_pos Real.pi_pos (by norm_num)),
      abs_of_pos (by linarith : 0 < 1 - x)]
    have hs := Real.abs_sinc_le_one (Real.pi * (x + 1) / 2)
    have hden : 0 < 1 - x := by linarith
    apply (div_le_iff₀ hden).2
    nlinarith [Real.pi_pos]

private theorem cosineRatio_integrable :
    Integrable
      (fun x : ℝ => Real.cos (Real.pi * x / 2) / (1 - x ^ 2)) := by
  let g : ℝ → ℝ := fun x =>
    (5 * (Real.pi / 2) + 2) * (1 + x ^ 2)⁻¹
  have hg : Integrable g :=
    integrable_inv_one_add_sq.const_mul (5 * (Real.pi / 2) + 2)
  refine hg.mono' (by
    exact
      ((Real.measurable_cos.comp
        ((measurable_const.mul measurable_id).div measurable_const)).div
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
      |Real.cos (Real.pi * x / 2) / (1 - x ^ 2)| ≤ Real.pi / 2 :=
        cosineRatio_abs_le x
      _ ≤ (5 * (Real.pi / 2) + 2) * (1 + x ^ 2)⁻¹ := by
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
    have hcos : |Real.cos (Real.pi * x / 2)| ≤ 1 :=
      Real.abs_cos_le_one _
    rw [abs_div, habsden]
    calc
      |Real.cos (Real.pi * x / 2)| / (x ^ 2 - 1) ≤
          1 / (x ^ 2 - 1) :=
        (div_le_div_iff_of_pos_right hden2).2 hcos
      _ ≤ 2 / (1 + x ^ 2) := by
        apply (div_le_div_iff₀ hden2 hden).2
        linarith
      _ ≤ (5 * (Real.pi / 2) + 2) * (1 + x ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith [Real.pi_pos]

private theorem cutoffCosine_hasCompactSupport :
    HasCompactSupport cutoffCosine := by
  refine
    HasCompactSupport.intro
      (isCompact_Icc :
        IsCompact (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))) ?_
  intro x hx
  have hout : ¬|x| ≤ Real.pi / 2 := by
    intro hxa
    exact hx ⟨neg_le_of_abs_le hxa, le_of_abs_le hxa⟩
  simp [cutoffCosine, hout]

private theorem cutoffCosine_integrable :
    Integrable cutoffCosine :=
  gap1.integrable_of_hasCompactSupport cutoffCosine_hasCompactSupport

private theorem cutoffCosine_cos_integrable (k : ℝ) :
    Integrable (fun t : ℝ => cutoffCosine t * Real.cos (k * t)) := by
  apply cutoffCosine_integrable.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (k * t)

private theorem half_cosine_integral
    (k : ℝ) (hk : k ^ 2 ≠ 1) :
    (∫ t in Set.Ioi (0 : ℝ),
        cutoffCosine t * Real.cos (k * t)) =
      Real.cos (Real.pi * k / 2) / (1 - k ^ 2) := by
  let f : ℝ → ℝ := fun t =>
    cutoffCosine t * Real.cos (k * t)
  have hf : Integrable f := cutoffCosine_cos_integrable k
  have himproper :
      improperIntegral 0 f = ∫ t in Set.Ioi (0 : ℝ), f t := by
    apply improperIntegral_eq_of_hasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
  have heq := (gap4 k).trans (gap5 k hk)
  change
    2 / Real.pi * improperIntegral 0 f =
      2 * Real.cos (k * Real.pi / 2) /
        (Real.pi * (1 - k ^ 2)) at heq
  rw [himproper] at heq
  change
    (∫ t in Set.Ioi (0 : ℝ), f t) =
      Real.cos (Real.pi * k / 2) / (1 - k ^ 2)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : 1 - k ^ 2 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hk)
  field_simp [hpi, hden] at heq ⊢
  exact heq

private theorem full_cosine_integral
    (k : ℝ) (hk : k ^ 2 ≠ 1) :
    (∫ t : ℝ, cutoffCosine t * Real.cos (k * t)) =
      2 * (Real.cos (Real.pi * k / 2) / (1 - k ^ 2)) := by
  let r : ℝ → ℝ := fun t =>
    cutoffCosine t * Real.cos (k * t)
  have hr : Integrable r := cutoffCosine_cos_integrable k
  have hge (t : ℝ) : r (-t) = r t := by
    dsimp [r]
    rw [gap2 t]
    rw [show k * -t = -(k * t) by ring, Real.cos_neg]
  have habs (t : ℝ) : r |t| = r t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), hge]
  calc
    (∫ t : ℝ, cutoffCosine t * Real.cos (k * t)) =
        ∫ t : ℝ, r t := by rfl
    _ = ∫ t : ℝ, r |t| := by
      apply integral_congr_ae
      filter_upwards with t
      exact (habs t).symm
    _ = 2 * ∫ t in Set.Ioi (0 : ℝ), r t :=
      integral_comp_abs
    _ = 2 * (Real.cos (Real.pi * k / 2) / (1 - k ^ 2)) := by
      rw [half_cosine_integral k hk]

private theorem integral_sine_zero (k : ℝ) :
    (∫ t : ℝ, cutoffCosine t * Real.sin (k * t)) = 0 := by
  let r : ℝ → ℝ := fun t =>
    cutoffCosine t * Real.sin (k * t)
  have hr : Integrable r := by
    apply cutoffCosine_integrable.mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (k * t)
  have hneg := integral_neg_eq_self r volume
  have hpoint (t : ℝ) : r (-t) = -r t := by
    dsimp [r]
    rw [gap2 t]
    rw [show k * -t = -(k * t) by ring, Real.sin_neg]
    ring
  simp_rw [hpoint, integral_neg] at hneg
  change (∫ t : ℝ, r t) = 0
  linarith

private def cf (x : ℝ) : ℂ :=
  (cutoffCosine x : ℝ)

private theorem cf_integrable :
    Integrable cf :=
  cutoffCosine_integrable.ofReal

private theorem cf_fourier
    (w : ℝ) (hw : (2 * Real.pi * w) ^ 2 ≠ 1) :
    𝓕 cf w =
      ((2 * (Real.cos (Real.pi * (2 * Real.pi * w) / 2) /
        (1 - (2 * Real.pi * w) ^ 2)) : ℝ) : ℂ) := by
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
        cutoffCosine t * Real.cos ((2 * Real.pi * w) * t) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  have himPoint (t : ℝ) :
      (J t).im =
        -(cutoffCosine t * Real.sin ((2 * Real.pi * w) * t)) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  simp_rw [hrePoint, full_cosine_integral (2 * Real.pi * w) hw] at hre
  simp_rw [himPoint, integral_neg,
    integral_sine_zero (2 * Real.pi * w), neg_zero] at him
  apply Complex.ext
  · norm_cast
    exact hre.symm
  · norm_cast
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
    Real.cos (Real.pi * z / 2) / (1 - z ^ 2)
  have hq : Integrable q := cosineRatio_integrable
  have hscaled : Integrable (fun w : ℝ => q (c * w)) :=
    hq.comp_mul_left' hc
  have hreal : Integrable (fun w : ℝ => 2 * q (c * w)) :=
    hscaled.const_mul 2
  have hcomplex :
      Integrable (fun w : ℝ => ((2 * q (c * w) : ℝ) : ℂ)) :=
    hreal.ofReal
  apply hcomplex.congr
  filter_upwards [frequency_nonresonant_ae] with w hw
  dsimp [q, c]
  exact (cf_fourier w hw).symm

private theorem fourier_full_real (x : ℝ) :
    (∫ w : ℝ,
        2 * (Real.cos (Real.pi * (2 * Real.pi * w) / 2) /
          (1 - (2 * Real.pi * w) ^ 2)) *
          Real.cos (2 * Real.pi * w * x)) =
      cutoffCosine x := by
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
          2 * (Real.cos (Real.pi * (2 * Real.pi * w) / 2) /
            (1 - (2 * Real.pi * w) ^ 2)) *
            Real.cos (2 * Real.pi * w * x) := by
    filter_upwards [frequency_nonresonant_ae] with w hw
    dsimp [K]
    rw [cf_fourier w hw]
    have hR :
        (((2 * (Real.cos (Real.pi * (2 * Real.pi * w) / 2) /
          (1 - (2 * Real.pi * w) ^ 2)) : ℝ) : ℂ)).re =
          2 * (Real.cos (Real.pi * (2 * Real.pi * w) / 2) /
            (1 - (2 * Real.pi * w) ^ 2)) := by
      norm_cast
    have hI :
        (((2 * (Real.cos (Real.pi * (2 * Real.pi * w) / 2) /
          (1 - (2 * Real.pi * w) ^ 2)) : ℝ) : ℂ)).im = 0 := by
      norm_cast
    rw [hR, hI, mul_zero, sub_zero, Complex.exp_re]
    simp
    ring
  rw [integral_congr_ae hpoint] at htotal
  have hcfre : (cf x).re = cutoffCosine x := by
    change (((cutoffCosine x : ℝ) : ℂ)).re = cutoffCosine x
    norm_cast
  rw [hcfre] at htotal
  exact htotal

private theorem cosineKernel_integrable (x : ℝ) :
    Integrable
      (fun lam : ℝ =>
        Real.cos (lam * Real.pi / 2) / (1 - lam ^ 2) *
          Real.cos (lam * x)) := by
  have hratio :
      Integrable
        (fun lam : ℝ =>
          Real.cos (lam * Real.pi / 2) / (1 - lam ^ 2)) := by
    apply cosineRatio_integrable.congr
    filter_upwards with lam
    congr 2
    ring
  apply hratio.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with lam
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (lam * x)

private theorem inverse_cosine_half (x : ℝ) :
    cutoffCosine x =
      2 / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          Real.cos (lam * Real.pi / 2) / (1 - lam ^ 2) *
            Real.cos (lam * x) := by
  let g : ℝ → ℝ := fun lam =>
    Real.cos (lam * Real.pi / 2) / (1 - lam ^ 2) *
      Real.cos (lam * x)
  have hg : Integrable g := cosineKernel_integrable x
  have hge (lam : ℝ) : g (-lam) = g lam := by
    dsimp [g]
    rw [show -lam * Real.pi / 2 = -(lam * Real.pi / 2) by ring,
      show -lam * x = -(lam * x) by ring,
      Real.cos_neg, Real.cos_neg]
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
      (∫ w : ℝ, 2 * g (c * w)) = cutoffCosine x := by
    rw [← fourier_full_real x]
    apply integral_congr_ae
    filter_upwards with w
    dsimp [g, c]
    ring
  have hmain :
      1 / Real.pi *
          (2 * ∫ lam in Set.Ioi (0 : ℝ), g lam) =
        cutoffCosine x := by
    rw [← heven]
    exact hscale.symm.trans hfull
  change cutoffCosine x =
    2 / Real.pi * ∫ lam in Set.Ioi (0 : ℝ), g lam
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hmain ⊢
  linarith

theorem gap7 (x : ℝ) :
    cutoffCosine x =
      2 / Real.pi * improperIntegral 0
        (fun lam =>
          Real.cos (lam * Real.pi / 2) / (1 - lam ^ 2) *
            Real.cos (lam * x)) := by
  let g : ℝ → ℝ := fun lam =>
    Real.cos (lam * Real.pi / 2) / (1 - lam ^ 2) *
      Real.cos (lam * x)
  have hg : Integrable g := cosineKernel_integrable x
  have himproper :
      improperIntegral 0 g =
        ∫ lam in Set.Ioi (0 : ℝ), g lam := by
    apply improperIntegral_eq_of_hasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi 0 hg.integrableOn tendsto_id
  change cutoffCosine x = 2 / Real.pi * improperIntegral 0 g
  rw [himproper]
  exact inverse_cosine_half x

end

end ProofGap.Exercise3888
