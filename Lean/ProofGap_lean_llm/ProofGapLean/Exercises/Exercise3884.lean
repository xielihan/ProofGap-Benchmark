import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise3884

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform Interval Topology

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def triangleFunction (a h x : ℝ) : ℝ :=
  if |x| ≤ a then h * (1 - |x| / a) else 0

def cosineCoefficient (a h lam : ℝ) : ℝ :=
  2 / Real.pi * improperIntegral 0
    (fun ξ => triangleFunction a h ξ * Real.cos (lam * ξ))

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

private theorem hasDerivAt_antiderivative
    (a lam x : ℝ) (ha : a ≠ 0) (hlam : lam ≠ 0) :
    HasDerivAt
      (fun z : ℝ =>
        (1 - z / a) * Real.sin (lam * z) / lam -
          Real.cos (lam * z) / (a * lam ^ 2))
      ((1 - x / a) * Real.cos (lam * x)) x := by
  have hsin :
      HasDerivAt (fun z : ℝ => Real.sin (lam * z))
        (lam * Real.cos (lam * x)) x := by
    convert (Real.hasDerivAt_sin (lam * x)).comp x
      ((hasDerivAt_const x lam).mul (hasDerivAt_id x)) using 1 <;> ring
  have hcos :
      HasDerivAt (fun z : ℝ => Real.cos (lam * z))
        (-(lam * Real.sin (lam * x))) x := by
    convert (Real.hasDerivAt_cos (lam * x)).comp x
      ((hasDerivAt_const x lam).mul (hasDerivAt_id x)) using 1 <;> ring
  have hlin :
      HasDerivAt (fun z : ℝ => 1 - z / a) (-1 / a) x := by
    convert
      (hasDerivAt_const x 1).sub ((hasDerivAt_id x).div_const a) using 1 <;>
      ring
  have h :=
    ((hlin.mul hsin).div_const lam).sub
      (hcos.div_const (a * lam ^ 2))
  convert h using 1
  field_simp [ha, hlam]
  ring

theorem gap1 (a h : ℝ) (ha : 0 < a) :
    Function.Even (triangleFunction a h) := by
  intro x
  simp [triangleFunction]

theorem gap2 (a h lam : ℝ) (ha : 0 < a) :
    cosineCoefficient a h lam =
      2 / Real.pi * improperIntegral 0
        (fun ξ => triangleFunction a h ξ * Real.cos (lam * ξ)) := by
  rfl

theorem gap7 (a h : ℝ) (ha : 0 < a) :
    Continuous (triangleFunction a h) := by
  unfold triangleFunction
  refine
    (continuous_const.mul
      (continuous_const.sub (continuous_id.abs.div_const a))).if_le
      continuous_const continuous_id.abs continuous_const ?_
  intro x hx
  have ha0 : a ≠ 0 := ne_of_gt ha
  change h * (1 - |x| / a) = 0
  rw [hx]
  field_simp [ha0]
  ring

theorem gap3 (a h lam : ℝ) (ha : 0 < a) :
    2 / Real.pi * improperIntegral 0
        (fun ξ => triangleFunction a h ξ * Real.cos (lam * ξ)) =
      2 * h / Real.pi *
        ∫ ξ in (0 : ℝ)..a, (1 - ξ / a) * Real.cos (lam * ξ) := by
  let f : ℝ → ℝ := fun ξ =>
    triangleFunction a h ξ * Real.cos (lam * ξ)
  have hf : Continuous f := by
    dsimp [f]
    exact (gap7 a h ha).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have himproper :
      HasImproperIntegral 0 f (∫ ξ in (0 : ℝ)..a, f ξ) := by
    unfold HasImproperIntegral
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop a] with b hb
    have hzero : (∫ ξ in a..b, f ξ) = 0 := by
      calc
        (∫ ξ in a..b, f ξ) = ∫ _ξ in a..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro ξ hξ
          rw [Set.uIcc_of_le hb] at hξ
          dsimp [f]
          by_cases hξa : ξ ≤ a
          · have heq : ξ = a := le_antisymm hξa hξ.1
            subst ξ
            simp [triangleFunction, abs_of_nonneg ha.le, ha.ne']
          · have hξ0 : 0 ≤ ξ := ha.le.trans hξ.1
            have hout : ¬|ξ| ≤ a := by
              rw [abs_of_nonneg hξ0]
              exact hξa
            simp [triangleFunction, hout]
        _ = 0 := by simp
    calc
      (∫ ξ in (0 : ℝ)..b, f ξ) =
          (∫ ξ in (0 : ℝ)..a, f ξ) + ∫ ξ in a..b, f ξ := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
      _ = ∫ ξ in (0 : ℝ)..a, f ξ := by rw [hzero, add_zero]
  rw [improperIntegral_eq_of_hasImproperIntegral himproper]
  have hinside :
      (∫ ξ in (0 : ℝ)..a, f ξ) =
        h * ∫ ξ in (0 : ℝ)..a,
          (1 - ξ / a) * Real.cos (lam * ξ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le ha.le] at hξ
    dsimp [f]
    simp [triangleFunction, abs_of_nonneg hξ.1, hξ.2]
    ring
  rw [hinside]
  ring

theorem gap4 (a h lam : ℝ) (ha : 0 < a) (hlam : lam ≠ 0) :
    2 * h / Real.pi *
        ∫ ξ in (0 : ℝ)..a, (1 - ξ / a) * Real.cos (lam * ξ) =
      2 * h * (1 - Real.cos (a * lam)) /
        (Real.pi * a * lam ^ 2) := by
  let F : ℝ → ℝ := fun z =>
    (1 - z / a) * Real.sin (lam * z) / lam -
      Real.cos (lam * z) / (a * lam ^ 2)
  have hInt :
      (∫ ξ in (0 : ℝ)..a,
          (1 - ξ / a) * Real.cos (lam * ξ)) = F a - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro ξ _
      exact hasDerivAt_antiderivative a lam ξ ha.ne' hlam
    · exact
        ((continuous_const.sub (continuous_id.div_const a)).mul
          (Real.continuous_cos.comp
            (continuous_const.mul continuous_id))).intervalIntegrable 0 a
  rw [hInt]
  dsimp [F]
  simp [ha.ne']
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [ha.ne', hlam, hpi]
  rw [show lam * a = a * lam by ring]
  ring

theorem gap5 (a h lam : ℝ) (ha : 0 < a) (hlam : lam ≠ 0) :
    cosineCoefficient a h lam =
      2 * h * (1 - Real.cos (a * lam)) /
        (Real.pi * a * lam ^ 2) := by
  exact (gap2 a h lam ha).trans
    ((gap3 a h lam ha).trans (gap4 a h lam ha hlam))

private theorem triangleFunction_hasCompactSupport
    (a h : ℝ) :
    HasCompactSupport (triangleFunction a h) := by
  refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-a) a)) ?_
  intro x hx
  have hout : ¬|x| ≤ a := by
    intro hxa
    exact hx ⟨neg_le_of_abs_le hxa, le_of_abs_le hxa⟩
  simp [triangleFunction, hout]

private theorem triangleFunction_integrable
    (a h : ℝ) (ha : 0 < a) :
    Integrable (triangleFunction a h) :=
  (gap7 a h ha).integrable_of_hasCompactSupport
    (triangleFunction_hasCompactSupport a h)

private theorem triangleCos_integrable
    (a h k : ℝ) (ha : 0 < a) :
    Integrable
      (fun t : ℝ => triangleFunction a h t * Real.cos (k * t)) := by
  apply (triangleFunction_integrable a h ha).mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (k * t)

private theorem half_triangle_cosine
    (a h k : ℝ) (ha : 0 < a) (hk : k ≠ 0) :
    (∫ t in Set.Ioi (0 : ℝ),
        triangleFunction a h t * Real.cos (k * t)) =
      h * (1 - Real.cos (a * k)) / (a * k ^ 2) := by
  let f : ℝ → ℝ := fun t =>
    triangleFunction a h t * Real.cos (k * t)
  have hf : Integrable f := triangleCos_integrable a h k ha
  have himproper :
      improperIntegral 0 f = ∫ t in Set.Ioi (0 : ℝ), f t := by
    apply improperIntegral_eq_of_hasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
  have heq := (gap3 a h k ha).trans (gap4 a h k ha hk)
  change
    2 / Real.pi * improperIntegral 0 f =
      2 * h * (1 - Real.cos (a * k)) /
        (Real.pi * a * k ^ 2) at heq
  rw [himproper] at heq
  change
    (∫ t in Set.Ioi (0 : ℝ), f t) =
      h * (1 - Real.cos (a * k)) / (a * k ^ 2)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi, ha.ne', hk] at heq ⊢
  linarith

private theorem real_fourier_integral
    (a h w : ℝ) (ha : 0 < a) (hw : w ≠ 0) :
    (∫ t : ℝ,
        triangleFunction a h t * Real.cos (2 * Real.pi * t * w)) =
      2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
        (a * (2 * Real.pi * w) ^ 2) := by
  let k : ℝ := 2 * Real.pi * w
  have hk : k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
  let r : ℝ → ℝ := fun t =>
    triangleFunction a h t * Real.cos (k * t)
  have hr : Integrable r := triangleCos_integrable a h k ha
  have hge (t : ℝ) : r (-t) = r t := by
    dsimp [r]
    rw [gap1 a h ha t]
    rw [show k * -t = -(k * t) by ring, Real.cos_neg]
  have habs (t : ℝ) : r |t| = r t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), hge]
  have heven :
      (∫ t : ℝ, r t) =
        2 * ∫ t in Set.Ioi (0 : ℝ), r t := by
    calc
      (∫ t : ℝ, r t) =
          ∫ t : ℝ, r |t| := by
        apply integral_congr_ae
        filter_upwards with t
        exact (habs t).symm
      _ = 2 * ∫ t in Set.Ioi (0 : ℝ), r t :=
        integral_comp_abs
  calc
    (∫ t : ℝ,
        triangleFunction a h t * Real.cos (2 * Real.pi * t * w)) =
        ∫ t : ℝ, r t := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [r, k]
      congr 2
      ring
    _ = 2 * h * (1 - Real.cos (a * k)) / (a * k ^ 2) := by
      rw [heven, half_triangle_cosine a h k ha hk]
      ring
    _ = 2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
        (a * (2 * Real.pi * w) ^ 2) := by
      rfl

private theorem baseKernel_integrable (a : ℝ) :
    Integrable (fun x : ℝ => (1 - Real.cos (a * x)) / x ^ 2) := by
  let g : ℝ → ℝ := fun x => (a ^ 2 + 4) * (1 + x ^ 2)⁻¹
  have hg : Integrable g :=
    integrable_inv_one_add_sq.const_mul (a ^ 2 + 4)
  refine hg.mono' (by
    exact
      ((measurable_const.sub
        (Real.measurable_cos.comp (measurable_const.mul measurable_id))).div
          (measurable_id.pow_const 2)).aestronglyMeasurable) ?_
  filter_upwards with x
  have hnum0 : 0 ≤ 1 - Real.cos (a * x) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hker0 : 0 ≤ (1 - Real.cos (a * x)) / x ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hker0]
  dsimp [g]
  by_cases hx0 : x = 0
  · simp [hx0]
    positivity
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
  by_cases hx : |x| ≤ 1
  · have hx_sq : x ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one (a := x)).2 hx
    have hsmall : 1 - Real.cos (a * x) ≤ a ^ 2 * x ^ 2 / 2 := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := a * x)]
    have hkernel : (1 - Real.cos (a * x)) / x ^ 2 ≤ a ^ 2 / 2 := by
      apply (div_le_iff₀ hx2).2
      nlinarith
    have hden : 0 < 1 + x ^ 2 := by positivity
    calc
      (1 - Real.cos (a * x)) / x ^ 2 ≤ a ^ 2 / 2 := hkernel
      _ ≤ (a ^ 2 + 4) * (1 + x ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (le_div_iff₀ hden).2
        nlinarith [sq_nonneg a]
  · have hx_sq : 1 < x ^ 2 := by
      have habs : 1 < |x| := lt_of_not_ge hx
      rw [← sq_abs x]
      nlinarith
    have hlarge : 1 - Real.cos (a * x) ≤ 2 := by
      nlinarith [Real.neg_one_le_cos (a * x)]
    have hkernel : (1 - Real.cos (a * x)) / x ^ 2 ≤ 2 / x ^ 2 :=
      (div_le_div_iff_of_pos_right hx2).2 hlarge
    have hden : 0 < 1 + x ^ 2 := by positivity
    calc
      (1 - Real.cos (a * x)) / x ^ 2 ≤ 2 / x ^ 2 := hkernel
      _ ≤ (a ^ 2 + 4) * (1 + x ^ 2)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div]
        apply (div_le_div_iff₀ hx2 hden).2
        nlinarith [sq_nonneg a]

private def cf (a h x : ℝ) : ℂ :=
  (triangleFunction a h x : ℝ)

private theorem cf_integrable (a h : ℝ) (ha : 0 < a) :
    Integrable (cf a h) :=
  (triangleFunction_integrable a h ha).ofReal

private theorem integral_sine_zero
    (a h k : ℝ) (ha : 0 < a) :
    (∫ t : ℝ, triangleFunction a h t * Real.sin (k * t)) = 0 := by
  let s : ℝ → ℝ := fun t =>
    triangleFunction a h t * Real.sin (k * t)
  have hs : Integrable s := by
    apply (triangleFunction_integrable a h ha).mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (k * t)
  have hneg := integral_neg_eq_self s volume
  have hpoint (t : ℝ) : s (-t) = -s t := by
    dsimp [s]
    rw [gap1 a h ha t]
    rw [show k * -t = -(k * t) by ring, Real.sin_neg]
    ring
  simp_rw [hpoint, integral_neg] at hneg
  change (∫ t : ℝ, s t) = 0
  linarith

private theorem cf_fourier
    (a h w : ℝ) (ha : 0 < a) (hw : w ≠ 0) :
    𝓕 (cf a h) w =
      ((2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
        (a * (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let J : ℝ → ℂ := fun t =>
    Complex.exp ((-2 * Real.pi * t * w : ℝ) * Complex.I) *
      cf a h t
  change (∫ t : ℝ, J t) = _
  have hJ : Integrable J := by
    apply (cf_integrable a h ha).bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      rw [Complex.norm_exp]
      simp
  have hre := integral_re hJ
  have him := integral_im hJ
  change
    (∫ t : ℝ, (J t).re) = (∫ t : ℝ, J t).re at hre
  change
    (∫ t : ℝ, (J t).im) = (∫ t : ℝ, J t).im at him
  have hrePoint (t : ℝ) :
      (J t).re =
        triangleFunction a h t * Real.cos (2 * Real.pi * t * w) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  have himPoint (t : ℝ) :
      (J t).im =
        -(triangleFunction a h t *
          Real.sin ((2 * Real.pi * w) * t)) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  simp_rw [hrePoint] at hre
  simp_rw [himPoint, integral_neg,
    integral_sine_zero a h (2 * Real.pi * w) ha, neg_zero] at him
  have hreal := real_fourier_integral a h w ha hw
  apply Complex.ext
  · norm_cast
    rw [← hreal]
    exact hre.symm
  · norm_cast
    exact him.symm

private theorem explicitFourier_integrable
    (a h : ℝ) (ha : 0 < a) :
    Integrable
      (fun w : ℝ =>
        2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
          (a * (2 * Real.pi * w) ^ 2)) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  let q : ℝ → ℝ := fun z =>
    (1 - Real.cos (a * z)) / z ^ 2
  have hq : Integrable q := baseKernel_integrable a
  have hscaled : Integrable (fun w : ℝ => q (c * w)) :=
    hq.comp_mul_left' hc
  have hmul :
      Integrable (fun w : ℝ => (2 * h / a) * q (c * w)) :=
    hscaled.const_mul (2 * h / a)
  apply hmul.congr
  filter_upwards with w
  dsimp [q, c]
  field_simp [ha.ne']

private theorem cf_fourier_integrable
    (a h : ℝ) (ha : 0 < a) :
    Integrable (𝓕 (cf a h)) := by
  have hcomplex :
      Integrable
        (fun w : ℝ =>
          ((2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
            (a * (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)) :=
    (explicitFourier_integrable a h ha).ofReal
  apply hcomplex.congr
  filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
  exact (cf_fourier a h w ha hw).symm

private theorem fourier_full_real
    (a h x : ℝ) (ha : 0 < a) :
    (∫ w : ℝ,
        (2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
          (a * (2 * Real.pi * w) ^ 2)) *
          Real.cos (2 * Real.pi * w * x)) =
      triangleFunction a h x := by
  have hinv :=
    (cf_integrable a h ha).fourierInv_fourier_eq
      (cf_fourier_integrable a h ha)
      (v := x) (by
        unfold cf
        exact (Complex.continuous_ofReal.comp (gap7 a h ha)).continuousAt)
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 (cf a h) w
  have hinvK : (∫ w : ℝ, K w) = cf a h x := by
    rw [Real.fourierInv_eq'] at hinv
    have hinner (v : ℝ) : inner ℝ v x = v * x := by
      change x * v = v * x
      ring
    simp_rw [hinner] at hinv
    simpa [K, smul_eq_mul, RCLike.inner_apply, mul_comm, mul_left_comm,
      mul_assoc] using hinv
  have hK : Integrable K := by
    apply (cf_fourier_integrable a h ha).bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with w
      rw [Complex.norm_exp]
      simp
  have hre := integral_re hK
  change
    (∫ w : ℝ, (K w).re) = (∫ w : ℝ, K w).re at hre
  have hreval := congrArg Complex.re hinvK
  have htotal := hre.trans hreval
  have hpoint :
      ∀ᵐ w : ℝ,
        (K w).re =
          (2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
            (a * (2 * Real.pi * w) ^ 2)) *
            Real.cos (2 * Real.pi * w * x) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
    dsimp [K]
    rw [cf_fourier a h w ha hw]
    have hR :
        (((2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
          (a * (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)).re =
          2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
            (a * (2 * Real.pi * w) ^ 2) := by
      norm_cast
    have hI :
        (((2 * h * (1 - Real.cos (a * (2 * Real.pi * w))) /
          (a * (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)).im = 0 := by
      norm_cast
    rw [hR, hI, mul_zero, sub_zero, Complex.exp_re]
    simp
    ring
  rw [integral_congr_ae hpoint] at htotal
  have hcfre : (cf a h x).re = triangleFunction a h x := by
    change (((triangleFunction a h x : ℝ) : ℂ)).re =
      triangleFunction a h x
    norm_cast
  rw [hcfre] at htotal
  exact htotal

private theorem oscillatoryKernel_integrable
    (a x : ℝ) :
    Integrable
      (fun lam : ℝ =>
        (1 - Real.cos (a * lam)) / lam ^ 2 *
          Real.cos (lam * x)) := by
  apply (baseKernel_integrable a).mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with lam
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (lam * x)

private theorem inverse_cosine_half
    (a h x : ℝ) (ha : 0 < a) :
    triangleFunction a h x =
      2 * h / (Real.pi * a) *
        ∫ lam in Set.Ioi (0 : ℝ),
          (1 - Real.cos (a * lam)) / lam ^ 2 *
            Real.cos (lam * x) := by
  let g : ℝ → ℝ := fun lam =>
    (1 - Real.cos (a * lam)) / lam ^ 2 *
      Real.cos (lam * x)
  have hg : Integrable g := oscillatoryKernel_integrable a x
  have hge (lam : ℝ) : g (-lam) = g lam := by
    dsimp [g]
    rw [show a * -lam = -(a * lam) by ring,
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
      (∫ w : ℝ, (2 * h / a) * g (c * w)) =
        (2 * h / a) / (2 * Real.pi) * ∫ lam : ℝ, g lam := by
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.2 hc)]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  have hfull :
      (∫ w : ℝ, (2 * h / a) * g (c * w)) =
        triangleFunction a h x := by
    rw [← fourier_full_real a h x ha]
    apply integral_congr_ae
    filter_upwards with w
    dsimp [g, c]
    field_simp [ha.ne']
  have hmain :
      (2 * h / a) / (2 * Real.pi) *
          (2 * ∫ lam in Set.Ioi (0 : ℝ), g lam) =
        triangleFunction a h x := by
    rw [← heven]
    exact hscale.symm.trans hfull
  change triangleFunction a h x =
    2 * h / (Real.pi * a) *
      ∫ lam in Set.Ioi (0 : ℝ), g lam
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [ha.ne', hpi] at hmain ⊢
  linarith

theorem gap6 (a h x : ℝ) (ha : 0 < a) :
    triangleFunction a h x =
      2 * h / (Real.pi * a) * improperIntegral 0
        (fun lam =>
          (1 - Real.cos (a * lam)) / lam ^ 2 * Real.cos (lam * x)) := by
  let g : ℝ → ℝ := fun lam =>
    (1 - Real.cos (a * lam)) / lam ^ 2 * Real.cos (lam * x)
  have hg : Integrable g := oscillatoryKernel_integrable a x
  have himproper :
      improperIntegral 0 g =
        ∫ lam in Set.Ioi (0 : ℝ), g lam := by
    apply improperIntegral_eq_of_hasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi 0 hg.integrableOn tendsto_id
  change triangleFunction a h x =
    2 * h / (Real.pi * a) * improperIntegral 0 g
  rw [himproper]
  exact inverse_cosine_half a h x ha

end

end ProofGap.Exercise3884
