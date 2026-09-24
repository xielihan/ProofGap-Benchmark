import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ProofGap.Exercise3896

noncomputable section

open MeasureTheory
open scoped FourierTransform

def fourierTransform (α x : ℝ) : ℂ :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      (Real.exp (-α * |t|) : ℂ) *
        Complex.exp (-(Complex.I * (t * x : ℝ)))

private theorem expAbs_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun t : ℝ => Real.exp (-α * |t|)) := by
  have hi₁ :
      IntegrableOn (fun t : ℝ => Real.exp ((-α) * t))
        (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hα) 0
  have hi :
      IntegrableOn (fun t : ℝ => Real.exp (-α * |t|))
        (Set.Ioi 0) := by
    apply hi₁.congr_fun
    · intro t ht
      change 0 < t at ht
      simp [abs_of_pos ht]
    · exact measurableSet_Ioi
  have hc₁ :
      IntegrableOn (fun t : ℝ => Real.exp (α * t))
        (Set.Iic 0) :=
    integrableOn_exp_mul_Iic hα 0
  have hc :
      IntegrableOn (fun t : ℝ => Real.exp (-α * |t|))
        (Set.Iic 0) := by
    apply hc₁.congr_fun
    · intro t ht
      change t ≤ 0 at ht
      simp [abs_of_nonpos ht]
    · exact measurableSet_Iic
  rw [← integrableOn_univ]
  rw [← Set.Ioi_union_Iic (a := (0 : ℝ))]
  exact hi.union hc

private theorem oscillatory_integrable (α x : ℝ) (hα : 0 < α) :
    Integrable (fun t : ℝ =>
      (Real.exp (-α * |t|) : ℂ) *
        Complex.exp (-(Complex.I * (t * x : ℝ)))) := by
  have hbase :
      Integrable (fun t : ℝ => (Real.exp (-α * |t|) : ℂ)) :=
    (expAbs_integrable α hα).ofReal
  apply hbase.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    rw [Complex.norm_exp]
    simp

private theorem sine_part_integrable (α x : ℝ) (hα : 0 < α) :
    Integrable (fun t : ℝ =>
      Real.exp (-α * |t|) * Real.sin (t * x)) := by
  apply (expAbs_integrable α hα).mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with t
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (t * x)

private theorem integral_sine_part (α x : ℝ) (hα : 0 < α) :
    (∫ t : ℝ, Real.exp (-α * |t|) * Real.sin (t * x)) = 0 := by
  let s : ℝ → ℝ := fun t =>
    Real.exp (-α * |t|) * Real.sin (t * x)
  have hs : Integrable s := sine_part_integrable α x hα
  have hneg := integral_neg_eq_self s volume
  have hpoint (t : ℝ) : s (-t) = -s t := by
    dsimp [s]
    rw [abs_neg, show (-t) * x = -(t * x) by ring, Real.sin_neg]
    ring
  simp_rw [hpoint] at hneg
  rw [integral_neg] at hneg
  change (∫ t : ℝ, s t) = 0
  linarith

private theorem laplace_cos (α x : ℝ) (hα : 0 < α) :
    (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-α * t) * Real.cos (t * x)) =
      α / (α ^ 2 + x ^ 2) := by
  let a : ℂ := (-α : ℝ) + (x : ℂ) * Complex.I
  have ha : a.re < 0 := by
    simp [a, hα]
  have hi :
      IntegrableOn (fun t : ℝ => Complex.exp (a * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have hre := integral_re hi
  change
    (∫ t in Set.Ioi (0 : ℝ), (Complex.exp (a * t)).re) =
      (∫ t in Set.Ioi (0 : ℝ), Complex.exp (a * t)).re at hre
  have heval := integral_exp_mul_complex_Ioi ha 0
  have hreval := congrArg Complex.re heval
  have hpoint (t : ℝ) :
      (Complex.exp (a * t)).re =
        Real.exp (-α * t) * Real.cos (t * x) := by
    rw [Complex.exp_re]
    simp [a]
    congr 1
    ring
  simp_rw [hpoint] at hre
  have htotal := hre.trans hreval
  rw [htotal]
  simp [Complex.div_re, Complex.normSq_apply, a]
  ring

theorem gap1 (α x : ℝ) (hα : 0 < α) :
    fourierTransform α x =
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (Real.exp (-α * |t|) : ℂ) *
            Complex.exp (-(Complex.I * (t * x : ℝ))) := by
  rfl

theorem gap2 (α x : ℝ) (hα : 0 < α) :
    ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Real.exp (-α * |t|) : ℂ) *
            Complex.exp (-(Complex.I * (t * x : ℝ)))) =
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (Real.exp (-α * |t|) : ℂ) *
            ((Real.cos (t * x) : ℂ) -
              Complex.I * (Real.sin (t * x) : ℂ)) := by
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  rw [show -(Complex.I * (t * x : ℝ)) =
    ((-(t * x) : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
  rw [Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring

theorem gap3 (α x : ℝ) (hα : 0 < α) :
    fourierTransform α x =
      ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          (Real.exp (-α * |t|) : ℂ) *
            ((Real.cos (t * x) : ℂ) -
              Complex.I * (Real.sin (t * x) : ℂ)) := by
  exact (gap1 α x hα).trans (gap2 α x hα)

theorem gap4 (α x : ℝ) (hα : 0 < α) :
    fourierTransform α x =
      (((1 / Real.sqrt (2 * Real.pi) : ℝ) *
        ∫ t : ℝ, Real.exp (-α * |t|) * Real.cos (t * x)) : ℂ) := by
  rw [gap3 α x hα]
  congr 1
  let K : ℝ → ℂ := fun t =>
    (Real.exp (-α * |t|) : ℂ) *
      ((Real.cos (t * x) : ℂ) -
        Complex.I * (Real.sin (t * x) : ℂ))
  have hK : Integrable K := by
    have hbase :
        Integrable (fun t : ℝ => (Real.exp (-α * |t|) : ℂ)) :=
      (expAbs_integrable α hα).ofReal
    apply hbase.mul_bdd (c := 2)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      rw [show
        ((Real.cos (t * x) : ℂ) -
            Complex.I * (Real.sin (t * x) : ℂ)) =
          Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) by
        rw [Complex.exp_mul_I]
        simp
        ring]
      rw [Complex.norm_exp]
      norm_num
  have hre := integral_re hK
  have him := integral_im hK
  change
    (∫ t : ℝ, (K t).re) = (∫ t : ℝ, K t).re at hre
  change
    (∫ t : ℝ, (K t).im) = (∫ t : ℝ, K t).im at him
  have hrePoint (t : ℝ) :
      (K t).re = Real.exp (-α * |t|) * Real.cos (t * x) := by
    dsimp [K]
    simp
  have himPoint (t : ℝ) :
      (K t).im = -(Real.exp (-α * |t|) * Real.sin (t * x)) := by
    dsimp [K]
    simp
  simp_rw [hrePoint] at hre
  simp_rw [himPoint, integral_neg, integral_sine_part α x hα, neg_zero] at him
  apply Complex.ext
  · simpa [K] using hre.symm
  · simpa [K] using him.symm

theorem gap5 (α x : ℝ) (hα : 0 < α) :
    1 / Real.sqrt (2 * Real.pi) *
        (∫ t : ℝ, Real.exp (-α * |t|) * Real.cos (t * x)) =
      Real.sqrt (2 / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-α * t) * Real.cos (t * x) := by
  let g : ℝ → ℝ := fun t =>
    Real.exp (-α * |t|) * Real.cos (t * x)
  have hg : Integrable g := by
    apply (expAbs_integrable α hα).mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)
  have habs (t : ℝ) : g |t| = g t := by
    dsimp [g]
    rw [abs_abs]
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      simp
  have heven :
      (∫ t : ℝ, g t) =
        2 * ∫ t in Set.Ioi (0 : ℝ), g t := by
    calc
      (∫ t : ℝ, g t) =
          ∫ t : ℝ, g |t| := by
        apply integral_congr_ae
        filter_upwards with t
        exact (habs t).symm
      _ = 2 * ∫ t in Set.Ioi (0 : ℝ), g t :=
        integral_comp_abs
  have hhalf :
      (∫ t in Set.Ioi (0 : ℝ), g t) =
        ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-α * t) * Real.cos (t * x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    simp [g, abs_of_pos ht]
  have hsqrt :
      2 / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hq : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hs : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
    have hqSq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
      Real.sq_sqrt (by positivity)
    have hsSq : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
      Real.sq_sqrt (by positivity)
    have hleft : 0 ≤ 2 / Real.sqrt (2 * Real.pi) := by positivity
    have hsq :
        (2 / Real.sqrt (2 * Real.pi)) ^ 2 = 2 / Real.pi := by
      field_simp [hq.ne', Real.pi_ne_zero]
      nlinarith
    nlinarith
  change
    1 / Real.sqrt (2 * Real.pi) * (∫ t : ℝ, g t) =
      Real.sqrt (2 / Real.pi) *
        ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-α * t) * Real.cos (t * x)
  rw [heven, hhalf]
  rw [← hsqrt]
  ring

theorem gap6 (α x : ℝ) (hα : 0 < α) :
    Real.sqrt (2 / Real.pi) *
        (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-α * t) * Real.cos (t * x)) =
      Real.sqrt (2 / Real.pi) * (α / (α ^ 2 + x ^ 2)) := by
  rw [laplace_cos α x hα]

theorem gap7 (α x : ℝ) (hα : 0 < α) :
    fourierTransform α x =
      ((Real.sqrt (2 / Real.pi) * (α / (α ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
  rw [gap4 α x hα]
  norm_cast
  exact (gap5 α x hα).trans (gap6 α x hα)

private def cf (α x : ℝ) : ℂ := (Real.exp (-α * |x|) : ℝ)

private theorem cf_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (cf α) := by
  exact (expAbs_integrable α hα).ofReal

private theorem cf_fourier (α w : ℝ) (hα : 0 < α) :
    𝓕 (cf α) w =
      ((2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let J : ℝ → ℂ := fun x =>
    Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) * cf α x
  have hJ : Integrable J := by
    apply (cf_integrable α hα).bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp
  have hsplit := integral_add_compl (s := Set.Ioi (0 : ℝ))
    measurableSet_Ioi hJ
  rw [Set.compl_Ioi] at hsplit
  change (∫ x : ℝ, J x) = _
  rw [← hsplit]
  let apos : ℂ := (-α : ℝ) - (2 * Real.pi * w : ℝ) * Complex.I
  let aneg : ℂ := (α : ℝ) - (2 * Real.pi * w : ℝ) * Complex.I
  have hapos : apos.re < 0 := by simp [apos, hα]
  have haneg : 0 < aneg.re := by simp [aneg, hα]
  have hplus :
      (∫ x in Set.Ioi (0 : ℝ), J x) =
        -(1 : ℂ) / apos := by
    calc
      (∫ x in Set.Ioi (0 : ℝ), J x) =
          ∫ x in Set.Ioi (0 : ℝ), Complex.exp (apos * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change 0 < x at hx
        dsimp [J, cf]
        rw [abs_of_pos hx]
        rw [show
          apos * (x : ℂ) =
            ((-α * x : ℝ) : ℂ) +
              ((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I by
          dsimp [apos]
          push_cast
          ring]
        rw [Complex.exp_add]
        simp
        ring
      _ = -(1 : ℂ) / apos := by
        simpa using integral_exp_mul_complex_Ioi hapos 0
  have hminus :
      (∫ x in Set.Iic (0 : ℝ), J x) =
        (1 : ℂ) / aneg := by
    calc
      (∫ x in Set.Iic (0 : ℝ), J x) =
          ∫ x in Set.Iic (0 : ℝ), Complex.exp (aneg * x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        change x ≤ 0 at hx
        dsimp [J, cf]
        rw [abs_of_nonpos hx]
        rw [show
          aneg * (x : ℂ) =
            ((α * x : ℝ) : ℂ) +
              ((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I by
          dsimp [aneg]
          push_cast
          ring]
        rw [Complex.exp_add]
        simp
        ring
      _ = (1 : ℂ) / aneg := by
        simpa using integral_exp_mul_complex_Iic haneg 0
  rw [hplus, hminus]
  have hden :
      (α ^ 2 + (2 * Real.pi * w) ^ 2 : ℝ) ≠ 0 := by
    positivity
  simp only [div_eq_mul_inv, one_mul, neg_mul]
  rw [Complex.inv_def, Complex.inv_def]
  simp [Complex.normSq_apply, apos, aneg]
  field_simp [hden]
  ring

private theorem cf_fourier_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (𝓕 (cf α)) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hc : 2 * Real.pi / α ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hα0
  have hscale :
      Integrable
        (fun w : ℝ => (1 + ((2 * Real.pi / α) * w) ^ 2)⁻¹) := by
    simpa only [mul_assoc] using
      integrable_inv_one_add_sq.comp_mul_left' hc
  have hreal :
      Integrable
        (fun w : ℝ => 2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2)) := by
    have hconst := hscale.const_mul (2 / α)
    apply hconst.congr
    filter_upwards with w
    field_simp [hα0]
  have hcomplex :
      Integrable
        (fun w : ℝ =>
          ((2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)) :=
    hreal.ofReal
  apply hcomplex.congr
  filter_upwards with w
  exact (cf_fourier α w hα).symm

private theorem fourier_full_real (α x : ℝ) (hα : 0 < α) :
    (∫ w : ℝ,
        2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2) *
          Real.cos (2 * Real.pi * w * x)) =
      Real.exp (-α * |x|) := by
  have hinv :=
    (cf_integrable α hα).fourierInv_fourier_eq
      (cf_fourier_integrable α hα)
      (v := x) (by
        unfold cf
        fun_prop)
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 (cf α) w
  have hinvK : (∫ w : ℝ, K w) = cf α x := by
    rw [Real.fourierInv_eq'] at hinv
    have hinner (v : ℝ) : inner ℝ v x = v * x := by
      change x * v = v * x
      ring
    simp_rw [hinner] at hinv
    simpa [K, smul_eq_mul, RCLike.inner_apply, mul_comm, mul_left_comm,
      mul_assoc] using hinv
  have hK : Integrable K := by
    apply (cf_fourier_integrable α hα).bdd_mul (c := 1)
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
  have hpoint (w : ℝ) :
      (K w).re =
        2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2) *
          Real.cos (2 * Real.pi * w * x) := by
    dsimp [K]
    rw [cf_fourier α w hα]
    have hR :
        (((2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)).re =
          2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2) := by
      norm_cast
    have hI :
        (((2 * α / (α ^ 2 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)).im = 0 := by
      norm_cast
    rw [hR, hI, mul_zero, sub_zero, Complex.exp_re]
    simp
    ring
  simp_rw [hpoint] at htotal
  have hcfre : (cf α x).re = Real.exp (-α * |x|) := by
    change (((Real.exp (-α * |x|) : ℝ) : ℂ)).re =
      Real.exp (-α * |x|)
    norm_cast
  rw [hcfre] at htotal
  exact htotal

private theorem cauchy_cos_half (α x : ℝ) (hα : 0 < α) :
    (∫ lam in Set.Ioi (0 : ℝ),
        α * Real.cos (lam * x) / (α ^ 2 + lam ^ 2)) =
      Real.pi / 2 * Real.exp (-α * |x|) := by
  let g : ℝ → ℝ := fun lam =>
    α * Real.cos (lam * x) / (α ^ 2 + lam ^ 2)
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hg : Integrable g := by
    have hscale :
        Integrable
          (fun lam : ℝ => (1 + (lam / α) ^ 2)⁻¹) := by
      simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hα0)
    have hbase :
        Integrable (fun lam : ℝ => (1 / α) * (1 + (lam / α) ^ 2)⁻¹) :=
      hscale.const_mul (1 / α)
    have hrational :
        Integrable (fun lam : ℝ => α / (α ^ 2 + lam ^ 2)) := by
      apply hbase.congr
      filter_upwards with lam
      field_simp [hα0]
    have hcosMeas :
        AEStronglyMeasurable (fun lam : ℝ => Real.cos (lam * x)) :=
      (by
        apply Continuous.aestronglyMeasurable
        fun_prop)
    have hcosBound :
        ∀ᵐ lam : ℝ, ‖Real.cos (lam * x)‖ ≤ (1 : ℝ) := by
      filter_upwards with lam
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (lam * x)
    have hprod :
        Integrable (fun lam : ℝ =>
          (α / (α ^ 2 + lam ^ 2)) * Real.cos (lam * x)) :=
      hrational.mul_bdd hcosMeas hcosBound
    apply hprod.congr
    filter_upwards with lam
    dsimp [g]
    ring
  have hge (lam : ℝ) : g (-lam) = g lam := by
    dsimp [g]
    rw [show (-lam) * x = -(lam * x) by ring, Real.cos_neg]
    ring_nf
  have habs (lam : ℝ) : g |lam| = g lam := by
    by_cases h : 0 ≤ lam
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), hge]
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
        (1 / Real.pi) * ∫ lam : ℝ, g lam := by
    rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.2 hc)]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  have hfull :
      (∫ w : ℝ, 2 * g (c * w)) = Real.exp (-α * |x|) := by
    rw [← fourier_full_real α x hα]
    apply integral_congr_ae
    filter_upwards with w
    dsimp [g, c]
    ring
  have hmain :
      (1 / Real.pi) *
          (2 * ∫ lam in Set.Ioi (0 : ℝ), g lam) =
        Real.exp (-α * |x|) := by
    rw [← heven]
    exact hscale.symm.trans hfull
  change (∫ lam in Set.Ioi (0 : ℝ), g lam) =
    Real.pi / 2 * Real.exp (-α * |x|)
  field_simp [Real.pi_ne_zero] at hmain ⊢
  linarith

theorem gap8 (α x : ℝ) (hα : 0 < α) :
    Real.exp (-α * |x|) =
      2 / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          α * Real.cos (lam * x) / (α ^ 2 + lam ^ 2) := by
  rw [cauchy_cos_half α x hα]
  field_simp [Real.pi_ne_zero]

end

end ProofGap.Exercise3896
