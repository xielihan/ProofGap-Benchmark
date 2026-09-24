import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ProofGap.Exercise3890

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

def expAbs (α x : ℝ) : ℝ :=
  Real.exp (-α * |x|)

def cosineTransform (f : ℝ → ℝ) (lam : ℝ) : ℝ :=
  2 / Real.pi *
    ∫ ξ in Set.Ioi (0 : ℝ), f ξ * Real.cos (lam * ξ)

private def cf (x : ℝ) : ℂ := (Real.exp (-|x|) : ℝ)

private theorem cf_integrable : Integrable cf := by
  have hi₁ :
      IntegrableOn (fun x : ℝ => Complex.exp ((-1 : ℂ) * x))
        (Set.Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (a := (-1 : ℂ)) (by norm_num) 0
  have hi :
      IntegrableOn cf (Set.Ioi 0) := by
    apply hi₁.congr_fun
    · intro x hx
      change 0 < x at hx
      simp [cf, abs_of_pos hx]
    · exact measurableSet_Ioi
  have hc₁ :
      IntegrableOn (fun x : ℝ => Complex.exp ((1 : ℂ) * x))
        (Set.Iic 0) :=
    integrableOn_exp_mul_complex_Iic (a := (1 : ℂ)) (by norm_num) 0
  have hc :
      IntegrableOn cf (Set.Iic 0) := by
    apply hc₁.congr_fun
    · intro x hx
      change x ≤ 0 at hx
      simp [cf, abs_of_nonpos hx]
    · exact measurableSet_Iic
  rw [← integrableOn_univ]
  rw [← Set.Ioi_union_Iic (a := (0 : ℝ))]
  exact hi.union hc

private theorem cf_fourier (w : ℝ) :
    𝓕 cf w =
      ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let J : ℝ → ℂ := fun x =>
    Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) * cf x
  have hJ : Integrable J := by
    apply cf_integrable.bdd_mul (c := 1)
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
  let apos : ℂ := (-1 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I
  let aneg : ℂ := (1 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I
  have hapos : apos.re < 0 := by simp [apos]
  have haneg : 0 < aneg.re := by simp [aneg]
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
            (-x : ℂ) +
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
            (x : ℂ) +
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
  have hden : (1 + (2 * Real.pi * w) ^ 2 : ℝ) ≠ 0 := by positivity
  simp only [div_eq_mul_inv, one_mul, neg_mul]
  rw [Complex.inv_def, Complex.inv_def]
  simp [Complex.normSq_apply, apos, aneg]
  field_simp [hden]
  ring

private theorem cf_fourier_integrable :
    Integrable (𝓕 cf) := by
  have hscale :
      Integrable
        (fun w : ℝ => (1 + (2 * Real.pi * w) ^ 2)⁻¹) := by
    simpa only [mul_assoc] using
      integrable_inv_one_add_sq.comp_mul_left'
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hreal :
      Integrable
        (fun w : ℝ => 2 / (1 + (2 * Real.pi * w) ^ 2)) := by
    simpa only [div_eq_mul_inv] using hscale.const_mul 2
  have hcomplex :
      Integrable
        (fun w : ℝ =>
          ((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)) :=
    hreal.ofReal
  apply hcomplex.congr
  filter_upwards with w
  exact (cf_fourier w).symm

private theorem fourier_full_real (x : ℝ) :
    (∫ w : ℝ,
        2 / (1 + (2 * Real.pi * w) ^ 2) *
          Real.cos (2 * Real.pi * w * x)) =
      Real.exp (-|x|) := by
  have hinv :=
    cf_integrable.fourierInv_fourier_eq cf_fourier_integrable
      (v := x) (by
        unfold cf
        fun_prop)
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
  change
    (∫ w : ℝ, (K w).re) = (∫ w : ℝ, K w).re at hre
  have hreval := congrArg Complex.re hinvK
  have htotal := hre.trans hreval
  have hpoint (w : ℝ) :
      (K w).re =
        2 / (1 + (2 * Real.pi * w) ^ 2) *
          Real.cos (2 * Real.pi * w * x) := by
    dsimp [K]
    rw [cf_fourier]
    have hR :
        (((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)).re =
          2 / (1 + (2 * Real.pi * w) ^ 2) := by
      norm_cast
    have hI :
        (((2 / (1 + (2 * Real.pi * w) ^ 2) : ℝ) : ℂ)).im = 0 := by
      norm_cast
    rw [hR, hI, mul_zero, sub_zero, Complex.exp_re]
    simp
    ring
  simp_rw [hpoint] at htotal
  have hcfre : (cf x).re = Real.exp (-|x|) := by
    change (((Real.exp (-|x|) : ℝ) : ℂ)).re = Real.exp (-|x|)
    norm_cast
  rw [hcfre] at htotal
  exact htotal

private theorem cauchy_cos_half (x : ℝ) :
    (∫ lam in Set.Ioi (0 : ℝ),
        Real.cos (lam * x) / (1 + lam ^ 2)) =
      Real.pi / 2 * Real.exp (-|x|) := by
  let g : ℝ → ℝ := fun lam =>
    Real.cos (lam * x) / (1 + lam ^ 2)
  have hg : Integrable g := by
    dsimp [g]
    have h :
        Integrable
          (fun lam : ℝ =>
            (1 + lam ^ 2)⁻¹ * Real.cos (lam * x)) := by
      apply integrable_inv_one_add_sq.mul_bdd (c := 1)
      · fun_prop
      · filter_upwards with lam
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (lam * x)
    simpa [div_eq_mul_inv, mul_comm] using h
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
        apply MeasureTheory.integral_congr_ae
        filter_upwards with lam
        exact (habs lam).symm
      _ = 2 * ∫ lam in Set.Ioi (0 : ℝ), g lam :=
        integral_comp_abs
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hscale :
      (∫ w : ℝ, 2 * g (c * w)) =
        (1 / Real.pi) * ∫ lam : ℝ, g lam := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.2 hc)]
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  have hfull :
      (∫ w : ℝ, 2 * g (c * w)) = Real.exp (-|x|) := by
    rw [← fourier_full_real x]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    dsimp [g, c]
    ring
  have hmain :
      (1 / Real.pi) *
          (2 * ∫ lam in Set.Ioi (0 : ℝ), g lam) =
        Real.exp (-|x|) := by
    rw [← heven]
    exact hscale.symm.trans hfull
  change (∫ lam in Set.Ioi (0 : ℝ), g lam) =
    Real.pi / 2 * Real.exp (-|x|)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hmain ⊢
  linarith

private theorem laplace_cos (α lam : ℝ) (hα : 0 < α) :
    (∫ ξ in Set.Ioi (0 : ℝ),
        Real.exp (-α * ξ) * Real.cos (lam * ξ)) =
      α / (lam ^ 2 + α ^ 2) := by
  let a : ℂ := (-α : ℝ) + (lam : ℂ) * Complex.I
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
        Real.exp (-α * x) * Real.cos (lam * x) := by
    rw [Complex.exp_re]
    simp [a]
  simp_rw [hpoint] at hre
  have htotal := hre.trans hreval
  rw [htotal]
  simp [Complex.div_re, Complex.normSq_apply, a]
  ring

private theorem scaled_cauchy_cos_half (α x : ℝ) (hα : 0 < α) :
    (∫ lam in Set.Ioi (0 : ℝ),
        Real.cos (lam * x) / (lam ^ 2 + α ^ 2)) =
      Real.pi / (2 * α) * Real.exp (-α * |x|) := by
  let g : ℝ → ℝ := fun lam =>
    Real.cos (lam * x) / (lam ^ 2 + α ^ 2)
  have hsubst :=
    integral_comp_mul_left_Ioi g 0 hα
  have hpoint (t : ℝ) :
      g (α * t) =
        (α ^ 2)⁻¹ * (Real.cos (t * (α * x)) / (1 + t ^ 2)) := by
    dsimp [g]
    have hα0 : α ≠ 0 := ne_of_gt hα
    field_simp [hα0]
    ring
  simp_rw [hpoint] at hsubst
  rw [MeasureTheory.integral_const_mul] at hsubst
  simp only [mul_zero, smul_eq_mul] at hsubst
  have hbase := cauchy_cos_half (α * x)
  have habs : |α * x| = α * |x| := by
    rw [abs_mul, abs_of_pos hα]
  rw [habs] at hbase
  rw [hbase] at hsubst
  change (∫ lam in Set.Ioi (0 : ℝ), g lam) =
    Real.pi / (2 * α) * Real.exp (-α * |x|)
  have hα0 : α ≠ 0 := ne_of_gt hα
  field_simp [hα0] at hsubst ⊢
  linarith

theorem gap1 (α : ℝ) (hα : 0 < α) :
    Continuous (expAbs α) := by
  unfold expAbs
  fun_prop

theorem gap2 (α : ℝ) (hα : 0 < α) :
    Function.Even (expAbs α) := by
  intro x
  simp [expAbs]

theorem gap3 (α : ℝ) (hα : 0 < α) :
    Integrable (expAbs α) := by
  have hi₁ :
      IntegrableOn (fun x : ℝ => Real.exp ((-α) * x))
        (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hα) 0
  have hi :
      IntegrableOn (expAbs α) (Set.Ioi 0) := by
    apply hi₁.congr_fun
    · intro x hx
      change 0 < x at hx
      simp [expAbs, abs_of_pos hx]
    · exact measurableSet_Ioi
  have hc₁ :
      IntegrableOn (fun x : ℝ => Real.exp (α * x))
        (Set.Iic 0) :=
    integrableOn_exp_mul_Iic hα 0
  have hc :
      IntegrableOn (expAbs α) (Set.Iic 0) := by
    apply hc₁.congr_fun
    · intro x hx
      change x ≤ 0 at hx
      simp [expAbs, abs_of_nonpos hx]
    · exact measurableSet_Iic
  rw [← integrableOn_univ]
  rw [← Set.Ioi_union_Iic (a := (0 : ℝ))]
  exact hi.union hc

theorem gap4 (f : ℝ → ℝ) (lam : ℝ) :
    cosineTransform f lam =
      2 / Real.pi *
        ∫ ξ in Set.Ioi (0 : ℝ), f ξ * Real.cos (lam * ξ) := by
  rfl

theorem gap5 (α lam : ℝ) :
    2 / Real.pi *
        (∫ ξ in Set.Ioi (0 : ℝ), expAbs α ξ * Real.cos (lam * ξ)) =
      2 / Real.pi *
        ∫ ξ in Set.Ioi (0 : ℝ),
          Real.exp (-α * ξ) * Real.cos (lam * ξ) := by
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ξ hξ
  change 0 < ξ at hξ
  simp [expAbs, abs_of_pos hξ]

theorem gap6 (α lam : ℝ) (hα : 0 < α) :
    2 / Real.pi *
        (∫ ξ in Set.Ioi (0 : ℝ),
          Real.exp (-α * ξ) * Real.cos (lam * ξ)) =
      2 * α / (Real.pi * (lam ^ 2 + α ^ 2)) := by
  rw [laplace_cos α lam hα]
  field_simp [Real.pi_ne_zero]

theorem gap7 (α lam : ℝ) (hα : 0 < α) :
    cosineTransform (expAbs α) lam =
      2 * α / (Real.pi * (lam ^ 2 + α ^ 2)) := by
  rw [gap4, gap5, gap6 α lam hα]

theorem gap8 (α x : ℝ) :
    expAbs α x = Real.exp (-α * |x|) := by
  rfl

theorem gap9 (α x : ℝ) (hα : 0 < α) :
    Real.exp (-α * |x|) =
      2 * α / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          Real.cos (lam * x) / (lam ^ 2 + α ^ 2) := by
  rw [scaled_cauchy_cos_half α x hα]
  field_simp [Real.pi_ne_zero, ne_of_gt hα]

theorem gap10 (α x : ℝ) (hα : 0 < α) :
    expAbs α x =
      2 * α / Real.pi *
        ∫ lam in Set.Ioi (0 : ℝ),
          Real.cos (lam * x) / (lam ^ 2 + α ^ 2) := by
  rw [gap8, gap9 α x hα]

end

end ProofGap.Exercise3890
