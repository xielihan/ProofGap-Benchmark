import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ProofGap.Exercise3892

noncomputable section

open MeasureTheory
open scoped FourierTransform

def dampedSine (α β x : ℝ) : ℝ :=
  Real.exp (-α * |x|) * Real.sin (β * x)

def sineTransform (f : ℝ → ℝ) (lam : ℝ) : ℝ :=
  2 / Real.pi *
    ∫ ξ in Set.Ioi (0 : ℝ), f ξ * Real.sin (lam * ξ)

private theorem expAbs_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun x : ℝ => Real.exp (-α * |x|)) := by
  have hi₁ :
      IntegrableOn (fun x : ℝ => Real.exp ((-α) * x))
        (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hα) 0
  have hi :
      IntegrableOn (fun x : ℝ => Real.exp (-α * |x|))
        (Set.Ioi 0) := by
    apply hi₁.congr_fun
    · intro x hx
      change 0 < x at hx
      simp [abs_of_pos hx]
    · exact measurableSet_Ioi
  have hc₁ :
      IntegrableOn (fun x : ℝ => Real.exp (α * x))
        (Set.Iic 0) :=
    integrableOn_exp_mul_Iic hα 0
  have hc :
      IntegrableOn (fun x : ℝ => Real.exp (-α * |x|))
        (Set.Iic 0) := by
    apply hc₁.congr_fun
    · intro x hx
      change x ≤ 0 at hx
      simp [abs_of_nonpos hx]
    · exact measurableSet_Iic
  rw [← integrableOn_univ]
  rw [← Set.Ioi_union_Iic (a := (0 : ℝ))]
  exact hi.union hc

private theorem laplace_cos_integrable (α k : ℝ) (hα : 0 < α) :
    IntegrableOn
      (fun ξ : ℝ => Real.exp (-α * ξ) * Real.cos (k * ξ))
      (Set.Ioi 0) := by
  have hbase :
      IntegrableOn (fun ξ : ℝ => Real.exp ((-α) * ξ)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hα) 0
  apply hbase.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with ξ
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (k * ξ)

private theorem laplace_cos (α k : ℝ) (hα : 0 < α) :
    (∫ ξ in Set.Ioi (0 : ℝ),
        Real.exp (-α * ξ) * Real.cos (k * ξ)) =
      α / (k ^ 2 + α ^ 2) := by
  let a : ℂ := (-α : ℝ) + (k : ℂ) * Complex.I
  have ha : a.re < 0 := by
    simp [a, hα]
  have hi :
      IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have hre := integral_re hi
  change
    (∫ x in Set.Ioi (0 : ℝ), (Complex.exp (a * x)).re) =
      (∫ x in Set.Ioi (0 : ℝ), Complex.exp (a * x)).re at hre
  have heval := integral_exp_mul_complex_Ioi ha 0
  have hreval := congrArg Complex.re heval
  have hpoint (x : ℝ) :
      (Complex.exp (a * x)).re =
        Real.exp (-α * x) * Real.cos (k * x) := by
    rw [Complex.exp_re]
    simp [a]
  simp_rw [hpoint] at hre
  have htotal := hre.trans hreval
  rw [htotal]
  simp [Complex.div_re, Complex.normSq_apply, a]
  ring

theorem gap1 (α β : ℝ) (hα : 0 < α) :
    Continuous (dampedSine α β) := by
  unfold dampedSine
  fun_prop

theorem gap2 (α β : ℝ) (hα : 0 < α) :
    Function.Odd (dampedSine α β) := by
  intro x
  simp [dampedSine]

theorem gap3 (α β : ℝ) (hα : 0 < α) :
    (∫ x : ℝ, Real.exp (-α * |x|) * |Real.sin (β * x)|) ≤
      ∫ x : ℝ, Real.exp (-α * |x|) := by
  have hbase := expAbs_integrable α hα
  have habsSin :
      AEStronglyMeasurable (fun x : ℝ => |Real.sin (β * x)|) :=
    (by
      apply Continuous.aestronglyMeasurable
      fun_prop)
  have hbound :
      ∀ᵐ x : ℝ, ‖(|Real.sin (β * x)| : ℝ)‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (β * x)
  have hleft :
      Integrable
        (fun x : ℝ => Real.exp (-α * |x|) * |Real.sin (β * x)|) :=
    hbase.mul_bdd habsSin hbound
  apply integral_mono hleft hbase
  intro x
  have hexp : 0 ≤ Real.exp (-α * |x|) := Real.exp_nonneg _
  nlinarith [Real.abs_sin_le_one (β * x)]

theorem gap4 (α : ℝ) (hα : 0 < α) :
    Integrable (fun x : ℝ => Real.exp (-α * |x|)) := by
  exact expAbs_integrable α hα

theorem gap5 (α β : ℝ) (hα : 0 < α) :
    Integrable (dampedSine α β) := by
  unfold dampedSine
  apply (expAbs_integrable α hα).mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (β * x)

theorem gap6 (f : ℝ → ℝ) (lam : ℝ) :
    sineTransform f lam =
      2 / Real.pi *
        ∫ ξ in Set.Ioi (0 : ℝ), f ξ * Real.sin (lam * ξ) := by
  rfl

theorem gap7 (α β lam : ℝ) :
    2 / Real.pi *
        (∫ ξ in Set.Ioi (0 : ℝ),
          dampedSine α β ξ * Real.sin (lam * ξ)) =
      2 / Real.pi *
        ∫ ξ in Set.Ioi (0 : ℝ),
          Real.exp (-α * ξ) * Real.sin (β * ξ) *
            Real.sin (lam * ξ) := by
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ξ hξ
  change 0 < ξ at hξ
  simp [dampedSine, abs_of_pos hξ]

theorem gap8 (α β lam : ℝ) :
    sineTransform (dampedSine α β) lam =
      2 / Real.pi *
        ∫ ξ in Set.Ioi (0 : ℝ),
          Real.exp (-α * ξ) * Real.sin (β * ξ) *
            Real.sin (lam * ξ) := by
  exact (gap6 (dampedSine α β) lam).trans (gap7 α β lam)

theorem gap9 (α β lam : ℝ) :
    sineTransform (dampedSine α β) lam =
      1 / Real.pi *
        ∫ ξ in Set.Ioi (0 : ℝ),
          (Real.cos ((lam - β) * ξ) - Real.cos ((lam + β) * ξ)) *
            Real.exp (-α * ξ) := by
  rw [gap8]
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ξ _
  dsimp only
  rw [show (lam - β) * ξ = lam * ξ - β * ξ by ring,
    show (lam + β) * ξ = lam * ξ + β * ξ by ring]
  rw [Real.cos_sub, Real.cos_add]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

theorem gap10 (α β lam : ℝ) (hα : 0 < α) :
    1 / Real.pi *
        (∫ ξ in Set.Ioi (0 : ℝ),
          (Real.cos ((lam - β) * ξ) - Real.cos ((lam + β) * ξ)) *
            Real.exp (-α * ξ)) =
      1 / Real.pi *
        (α / ((lam - β) ^ 2 + α ^ 2) -
          α / ((lam + β) ^ 2 + α ^ 2)) := by
  have hminus := laplace_cos_integrable α (lam - β) hα
  have hplus := laplace_cos_integrable α (lam + β) hα
  have hsplit :
      (∫ ξ in Set.Ioi (0 : ℝ),
          (Real.cos ((lam - β) * ξ) - Real.cos ((lam + β) * ξ)) *
            Real.exp (-α * ξ)) =
        (∫ ξ in Set.Ioi (0 : ℝ),
          Real.exp (-α * ξ) * Real.cos ((lam - β) * ξ)) -
        ∫ ξ in Set.Ioi (0 : ℝ),
          Real.exp (-α * ξ) * Real.cos ((lam + β) * ξ) := by
    rw [← MeasureTheory.integral_sub hminus hplus]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro ξ _
    ring
  rw [hsplit, laplace_cos α (lam - β) hα,
    laplace_cos α (lam + β) hα]

theorem gap11 (α β lam : ℝ) (hα : 0 < α) :
    sineTransform (dampedSine α β) lam =
      1 / Real.pi *
        (α / ((lam - β) ^ 2 + α ^ 2) -
          α / ((lam + β) ^ 2 + α ^ 2)) := by
  exact (gap9 α β lam).trans (gap10 α β lam hα)

theorem gap12 (α β lam : ℝ) (hα : 0 < α) :
    sineTransform (dampedSine α β) lam =
      4 * lam * α * β /
        (Real.pi * ((lam - β) ^ 2 + α ^ 2) *
          ((lam + β) ^ 2 + α ^ 2)) := by
  rw [gap11 α β lam hα]
  have hminus : (lam - β) ^ 2 + α ^ 2 ≠ 0 := by positivity
  have hplus : (lam + β) ^ 2 + α ^ 2 ≠ 0 := by positivity
  field_simp [hminus, hplus, Real.pi_ne_zero]
  ring

private def cf (α β x : ℝ) : ℂ := (dampedSine α β x : ℝ)

private theorem cf_integrable (α β : ℝ) (hα : 0 < α) :
    Integrable (cf α β) := by
  exact (gap5 α β hα).ofReal

private theorem integral_cosine_zero (α β k : ℝ) (hα : 0 < α) :
    (∫ t : ℝ, dampedSine α β t * Real.cos (k * t)) = 0 := by
  let s : ℝ → ℝ := fun t =>
    dampedSine α β t * Real.cos (k * t)
  have hs : Integrable s := by
    apply (gap5 α β hα).mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (k * t)
  have hneg := integral_neg_eq_self s volume
  have hpoint (t : ℝ) : s (-t) = -s t := by
    dsimp [s]
    rw [gap2 α β hα t]
    rw [show k * -t = -(k * t) by ring, Real.cos_neg]
    ring
  simp_rw [hpoint, integral_neg] at hneg
  change (∫ t : ℝ, s t) = 0
  linarith

private theorem real_sine_integral (α β k : ℝ) (hα : 0 < α) :
    (∫ t : ℝ, dampedSine α β t * Real.sin (k * t)) =
      α / ((k - β) ^ 2 + α ^ 2) -
        α / ((k + β) ^ 2 + α ^ 2) := by
  let r : ℝ → ℝ := fun t =>
    dampedSine α β t * Real.sin (k * t)
  have hr : Integrable r := by
    apply (gap5 α β hα).mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (k * t)
  have hge (t : ℝ) : r (-t) = r t := by
    dsimp [r]
    rw [gap2 α β hα t]
    rw [show k * -t = -(k * t) by ring, Real.sin_neg]
    ring
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
  have hst := gap11 α β k hα
  unfold sineTransform at hst
  have hhalf :
      2 * ∫ t in Set.Ioi (0 : ℝ), r t =
        α / ((k - β) ^ 2 + α ^ 2) -
          α / ((k + β) ^ 2 + α ^ 2) := by
    dsimp [r]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hpi] at hst ⊢
    linarith
  change (∫ t : ℝ, r t) = _
  rw [heven]
  exact hhalf

private theorem cf_fourier (α β w : ℝ) (hα : 0 < α) :
    𝓕 (cf α β) w =
      -(Complex.I *
        ((α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2) -
          α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2) : ℝ) : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let J : ℝ → ℂ := fun t =>
    Complex.exp ((-2 * Real.pi * t * w : ℝ) * Complex.I) *
      cf α β t
  change (∫ t : ℝ, J t) = _
  have hJ : Integrable J := by
    apply (cf_integrable α β hα).bdd_mul (c := 1)
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
        dampedSine α β t * Real.cos ((2 * Real.pi * w) * t) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  have himPoint (t : ℝ) :
      (J t).im =
        -(dampedSine α β t * Real.sin ((2 * Real.pi * w) * t)) := by
    dsimp [J, cf]
    rw [Complex.exp_re, Complex.exp_im]
    simp
    ring_nf
  simp_rw [hrePoint,
    integral_cosine_zero α β (2 * Real.pi * w) hα] at hre
  simp_rw [himPoint, integral_neg] at him
  have hsine := real_sine_integral α β (2 * Real.pi * w) hα
  let D : ℝ :=
    α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2) -
      α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2)
  change (∫ t : ℝ, J t) = -(Complex.I * ((D : ℝ) : ℂ))
  have hD :
      D = ∫ t : ℝ,
        dampedSine α β t * Real.sin ((2 * Real.pi * w) * t) := by
    dsimp [D]
    exact hsine.symm
  have hR :
      (-(Complex.I * ((D : ℝ) : ℂ))).re = 0 := by
    simp
  have hI :
      (-(Complex.I * ((D : ℝ) : ℂ))).im = -D := by
    simp
  apply Complex.ext
  · rw [hR]
    exact hre.symm
  · rw [hI, hD]
    exact him.symm

private theorem centered_cauchy_integrable (α : ℝ) (hα : 0 < α) :
    Integrable (fun z : ℝ => α / (z ^ 2 + α ^ 2)) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hscale :
      Integrable (fun z : ℝ => (1 + (z / α) ^ 2)⁻¹) := by
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hα0)
  have hbase :
      Integrable (fun z : ℝ => (1 / α) * (1 + (z / α) ^ 2)⁻¹) :=
    hscale.const_mul (1 / α)
  apply hbase.congr
  filter_upwards with z
  field_simp [hα0]
  ring

private theorem cf_fourier_integrable (α β : ℝ) (hα : 0 < α) :
    Integrable (𝓕 (cf α β)) := by
  let c : ℝ := 2 * Real.pi
  have hc : c ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  let q : ℝ → ℝ := fun z => α / (z ^ 2 + α ^ 2)
  have hq : Integrable q := centered_cauchy_integrable α hα
  have hminus :
      Integrable (fun w : ℝ =>
        α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2)) := by
    have h := (hq.comp_add_left (-β)).comp_mul_left' hc
    apply h.congr
    filter_upwards with w
    dsimp [q, c]
    congr 2
    ring
  have hplus :
      Integrable (fun w : ℝ =>
        α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2)) := by
    have h := (hq.comp_add_left β).comp_mul_left' hc
    simpa [q, c, add_comm] using h
  have hreal :
      Integrable (fun w : ℝ =>
        α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2) -
          α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2)) :=
    hminus.sub hplus
  have hcomplex :
      Integrable (fun w : ℝ =>
        -(Complex.I *
          ((α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2) -
            α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2) : ℝ) : ℂ))) := by
    simpa [neg_mul] using hreal.ofReal.const_mul (-Complex.I)
  apply hcomplex.congr
  filter_upwards with w
  exact (cf_fourier α β w hα).symm

private theorem fourier_full_real (α β x : ℝ) (hα : 0 < α) :
    (∫ w : ℝ,
        (α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2) -
          α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2)) *
          Real.sin (2 * Real.pi * w * x)) =
      dampedSine α β x := by
  have hinv :=
    (cf_integrable α β hα).fourierInv_fourier_eq
      (cf_fourier_integrable α β hα)
      (v := x) (by
        unfold cf dampedSine
        fun_prop)
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((2 * Real.pi * w * x : ℝ) : ℂ) * Complex.I) *
      𝓕 (cf α β) w
  have hinvK : (∫ w : ℝ, K w) = cf α β x := by
    rw [Real.fourierInv_eq'] at hinv
    have hinner (v : ℝ) : inner ℝ v x = v * x := by
      change x * v = v * x
      ring
    simp_rw [hinner] at hinv
    simpa [K, smul_eq_mul, RCLike.inner_apply, mul_comm, mul_left_comm,
      mul_assoc] using hinv
  have hK : Integrable K := by
    apply (cf_fourier_integrable α β hα).bdd_mul (c := 1)
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
        (α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2) -
          α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2)) *
          Real.sin (2 * Real.pi * w * x) := by
    dsimp [K]
    let D : ℝ :=
      α / ((2 * Real.pi * w - β) ^ 2 + α ^ 2) -
        α / ((2 * Real.pi * w + β) ^ 2 + α ^ 2)
    rw [show 𝓕 (cf α β) w = -(Complex.I * ((D : ℝ) : ℂ)) by
      exact cf_fourier α β w hα]
    simp [Complex.exp_re, Complex.exp_im]
    dsimp [D]
    ring
  simp_rw [hpoint] at htotal
  have hcfre : (cf α β x).re = dampedSine α β x := by
    change (((dampedSine α β x : ℝ) : ℂ)).re =
      dampedSine α β x
    norm_cast
  rw [hcfre] at htotal
  exact htotal

private theorem inverse_sine_half (α β x : ℝ) (hα : 0 < α) :
    dampedSine α β x =
      4 * α * β / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          lam * Real.sin (lam * x) /
            (((lam - β) ^ 2 + α ^ 2) *
              ((lam + β) ^ 2 + α ^ 2)) := by
  let d : ℝ → ℝ := fun lam =>
    α / ((lam - β) ^ 2 + α ^ 2) -
      α / ((lam + β) ^ 2 + α ^ 2)
  let g : ℝ → ℝ := fun lam => d lam * Real.sin (lam * x)
  let q : ℝ → ℝ := fun z => α / (z ^ 2 + α ^ 2)
  have hq : Integrable q := centered_cauchy_integrable α hα
  have hd : Integrable d := by
    have hm := hq.comp_add_right (-β)
    have hp := hq.comp_add_right β
    apply (hm.sub hp).congr
    filter_upwards with lam
    dsimp [d, q]
    congr 1 <;> congr 2 <;> ring
  have hg : Integrable g := by
    apply hd.mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards with lam
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (lam * x)
  have hde (lam : ℝ) : d (-lam) = -d lam := by
    dsimp [d]
    rw [show -lam - β = -(lam + β) by ring,
      show -lam + β = -(lam - β) by ring]
    ring_nf
  have hge (lam : ℝ) : g (-lam) = g lam := by
    dsimp [g]
    rw [hde, show -lam * x = -(lam * x) by ring, Real.sin_neg]
    ring
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
      (∫ w : ℝ, g (c * w)) =
        1 / (2 * Real.pi) * ∫ lam : ℝ, g lam := by
    rw [MeasureTheory.Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.2 hc)]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  have hfull :
      (∫ w : ℝ, g (c * w)) = dampedSine α β x := by
    rw [← fourier_full_real α β x hα]
  have hmain :
      1 / (2 * Real.pi) *
          (2 * ∫ lam in Set.Ioi (0 : ℝ), g lam) =
        dampedSine α β x := by
    rw [← heven]
    exact hscale.symm.trans hfull
  have hkernel :
      (∫ lam in Set.Ioi (0 : ℝ), g lam) =
        4 * α * β *
          ∫ lam in Set.Ioi (0 : ℝ),
            lam * Real.sin (lam * x) /
              (((lam - β) ^ 2 + α ^ 2) *
                ((lam + β) ^ 2 + α ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro lam _
    dsimp [g, d]
    have hm : (lam - β) ^ 2 + α ^ 2 ≠ 0 := by positivity
    have hp : (lam + β) ^ 2 + α ^ 2 ≠ 0 := by positivity
    field_simp [hm, hp]
    ring
  change dampedSine α β x =
    4 * α * β / Real.pi *
      ∫ lam in Set.Ioi (0 : ℝ),
        lam * Real.sin (lam * x) /
          (((lam - β) ^ 2 + α ^ 2) *
            ((lam + β) ^ 2 + α ^ 2))
  rw [hkernel] at hmain
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hmain ⊢
  simpa [mul_comm] using hmain.symm

theorem gap13 (α β x : ℝ) (hα : 0 < α) :
    Real.exp (-α * |x|) * Real.sin (β * x) =
      4 * α * β / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          lam * Real.sin (lam * x) /
            (((lam - β) ^ 2 + α ^ 2) *
              ((lam + β) ^ 2 + α ^ 2)) := by
  exact inverse_sine_half α β x hα

end

end ProofGap.Exercise3892
