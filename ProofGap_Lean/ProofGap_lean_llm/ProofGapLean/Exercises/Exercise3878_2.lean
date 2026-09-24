import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3878_2

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Topology

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ t in a..b, f t) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def baseKernel (lam x α t : ℝ) : ℝ :=
  Real.rpow t (x - 1) * Real.exp (-(lam * t) * Real.cos α)

def cosKernel (lam x α t : ℝ) : ℝ :=
  baseKernel lam x α t * Real.cos (lam * t * Real.sin α)

def sinKernel (lam x α t : ℝ) : ℝ :=
  baseKernel lam x α t * Real.sin (lam * t * Real.sin α)

def I (lam x α : ℝ) : ℝ :=
  improperIntegral 0 (cosKernel lam x α)

def I₁ (lam x α : ℝ) : ℝ :=
  improperIntegral 0 (sinKernel lam x α)

def evalAt (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  f a

private def complexRate (lam α : ℝ) : ℂ :=
  ((-lam * Real.cos α : ℝ) : ℂ) +
    ((lam * Real.sin α : ℝ) : ℂ) * Complex.I

private def complexKernel (x lam α t : ℝ) : ℂ :=
  ((Real.rpow t (x - 1) : ℝ) : ℂ) *
    Complex.exp (complexRate lam α * t)

private def complexValue (x lam α : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), complexKernel x lam α t

private def rateDerivative (lam α : ℝ) : ℂ :=
  ((lam * Real.sin α : ℝ) : ℂ) +
    ((lam * Real.cos α : ℝ) : ℂ) * Complex.I

private def angleDerivativeKernel (x lam α t : ℝ) : ℂ :=
  ((Real.rpow t (x - 1) : ℝ) : ℂ) *
    (Complex.exp (complexRate lam α * t) *
      (rateDerivative lam α * (t : ℂ)))

private def derivativeMajorant (x lam α t : ℝ) : ℝ :=
  2 * lam *
    (Real.rpow t x *
      Real.exp (-(lam * (Real.cos α / 2) * t)))

private theorem gammaWeight_integrable
    (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    IntegrableOn
      (fun t : ℝ =>
        Real.rpow t (x - 1) * Real.exp (-(c * t)))
      (Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun u =>
    Real.exp (-u) * Real.rpow u (x - 1)
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    simpa [f, mul_comm] using Real.GammaIntegral_convergent hx
  have hcomp :
      IntegrableOn (fun t : ℝ => f (c * t)) (Ioi (0 : ℝ)) := by
    have h :=
      (integrableOn_Ioi_comp_mul_left_iff f 0 hc).2
        (by simpa using hf)
    simpa using h
  have hscaled :=
    hcomp.const_mul (Real.rpow c (1 - x))
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  ·
    have ht0 : 0 < t := ht
    dsimp [f]
    rw [Real.mul_rpow hc.le ht0.le]
    have hp :
        Real.rpow c (1 - x) * Real.rpow c (x - 1) = 1 := by
      calc
        Real.rpow c (1 - x) * Real.rpow c (x - 1) =
            Real.rpow c ((1 - x) + (x - 1)) :=
          (Real.rpow_add hc (1 - x) (x - 1)).symm
        _ = 1 := by simp
    change
      Real.rpow c (1 - x) *
          (Real.exp (-(c * t)) *
            (Real.rpow c (x - 1) * Real.rpow t (x - 1))) =
        Real.rpow t (x - 1) * Real.exp (-(c * t))
    rw [show
      Real.rpow c (1 - x) *
          (Real.exp (-(c * t)) *
            (Real.rpow c (x - 1) * Real.rpow t (x - 1))) =
        (Real.rpow c (1 - x) * Real.rpow c (x - 1)) *
          (Real.rpow t (x - 1) * Real.exp (-(c * t))) by ring,
      hp, one_mul]

private theorem complexKernel_continuousOn
    (x lam α : ℝ) :
    ContinuousOn (complexKernel x lam α) (Ioi (0 : ℝ)) := by
  have hr :
      ContinuousOn (fun t : ℝ => Real.rpow t (x - 1))
        (Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt ht))
  have hrc :
      ContinuousOn
        (fun t : ℝ => ((Real.rpow t (x - 1) : ℝ) : ℂ))
        (Ioi (0 : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn hr
  unfold complexKernel
  exact hrc.mul
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).continuousOn

private theorem complexKernel_integrable
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    IntegrableOn (complexKernel x lam α) (Ioi (0 : ℝ)) := by
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo hα
  have hc : 0 < lam * Real.cos α :=
    mul_pos hlam hcos
  have hmajor :=
    gammaWeight_integrable x (lam * Real.cos α) hx hc
  refine hmajor.mono'
    ((complexKernel_continuousOn x lam α).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hrpow :
      0 < Real.rpow t (x - 1) :=
    Real.rpow_pos_of_pos ht0 (x - 1)
  unfold complexKernel complexRate
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hrpow,
    Complex.norm_exp]
  have hre :
      (((((-lam * Real.cos α : ℝ) : ℂ) +
        ((lam * Real.sin α : ℝ) : ℂ) * Complex.I) *
          (t : ℂ))).re =
        -(lam * Real.cos α * t) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]

private theorem complex_moment_relation
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (∫ t in Ioi (0 : ℝ),
        ((Real.rpow t x : ℝ) : ℂ) *
          (complexRate lam α *
            Complex.exp (complexRate lam α * t))) =
      -((x : ℂ) * complexValue x lam α) := by
  let z : ℂ := complexRate lam α
  let u : ℝ → ℂ := fun t => ((Real.rpow t x : ℝ) : ℂ)
  let u' : ℝ → ℂ :=
    fun t => (((x * Real.rpow t (x - 1) : ℝ) : ℂ))
  let v : ℝ → ℂ := fun t => Complex.exp (z * t)
  let v' : ℝ → ℂ := fun t => z * Complex.exp (z * t)
  have hu :
      ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := by
    intro t ht
    dsimp [u, u']
    convert
      (Real.hasDerivAt_rpow_const (p := x)
        (Or.inl (ne_of_gt ht))).ofReal_comp using 1
  have hv :
      ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
    intro t ht
    have hlin :
        HasDerivAt (fun s : ℝ => z * (s : ℂ)) z t := by
      convert
        (hasDerivAt_const t z).mul
          ((hasDerivAt_id t).ofReal_comp) using 1 <;> simp
    dsimp [v, v']
    simpa [mul_comm] using hlin.cexp
  have hbase :
      IntegrableOn (complexKernel x lam α) (Ioi (0 : ℝ)) :=
    complexKernel_integrable x lam α hx hlam hα
  have hnext :
      IntegrableOn (complexKernel (x + 1) lam α) (Ioi (0 : ℝ)) :=
    complexKernel_integrable (x + 1) lam α (by linarith) hlam hα
  have hu'v :
      IntegrableOn (u' * v) (Ioi (0 : ℝ)) := by
    have h := hbase.const_mul (x : ℂ)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [u', v, complexKernel, z]
    rw [Complex.ofReal_mul]
    ring
  have huv' :
      IntegrableOn (u * v') (Ioi (0 : ℝ)) := by
    have h := hnext.const_mul (complexRate lam α)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hrpow :
        Real.rpow t ((x + 1) - 1) = Real.rpow t x := by
      congr 1
      ring
    dsimp [u, v', complexKernel, z]
    change
      complexRate lam α *
          (((Real.rpow t ((x + 1) - 1) : ℝ) : ℂ) *
            Complex.exp (complexRate lam α * (t : ℂ))) =
        ((Real.rpow t x : ℝ) : ℂ) *
          (complexRate lam α *
            Complex.exp (complexRate lam α * (t : ℂ)))
    rw [hrpow]
    ring
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo hα
  have hc : 0 < lam * Real.cos α :=
    mul_pos hlam hcos
  have hzero :
      Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hp :
        Tendsto (fun t : ℝ => t ^ x)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h :=
        (Real.continuous_rpow_const hx.le).continuousAt
          (x := (0 : ℝ))
      have hfull :
          Tendsto (fun t : ℝ => t ^ x)
            (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa [Real.zero_rpow hx.ne'] using h.tendsto
      exact hfull.mono_left inf_le_left
    have he :
        Tendsto
          (fun t : ℝ =>
            Real.exp (-(lam * Real.cos α * t)))
          (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h :
          ContinuousAt
            (fun t : ℝ =>
              Real.exp (-(lam * Real.cos α * t))) 0 := by
        fun_prop
      simpa using h.tendsto.mono_left inf_le_left
    have hpe :
        Tendsto
          (fun t : ℝ =>
            t ^ x *
              Real.exp (-(lam * Real.cos α * t)))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hp.mul he
    apply hpe.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have hrpow :
        0 < t ^ x :=
      Real.rpow_pos_of_pos ht0 x
    dsimp [u, v, z]
    rw [norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpow, Complex.norm_exp]
    have hre :
        ((complexRate lam α * (t : ℂ)).re) =
          -(lam * Real.cos α * t) := by
      unfold complexRate
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre]
  have hinfty :
      Tendsto (u * v) atTop (𝓝 (0 : ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero x
        (lam * Real.cos α) hc
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hrpow :
        0 < t ^ x :=
      Real.rpow_pos_of_pos ht x
    dsimp [u, v, z]
    rw [norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpow, Complex.norm_exp]
    have hre :
        ((complexRate lam α * (t : ℂ)).re) =
          -(lam * Real.cos α * t) := by
      unfold complexRate
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre]
    congr 2
    ring
  have hparts :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (u := u) (u' := u')
      (v := v) (v' := v') hu hv huv' hu'v hzero hinfty
  have hint :
      (∫ t in Ioi (0 : ℝ), u' t * v t) =
        (x : ℂ) * complexValue x lam α := by
    unfold complexValue
    calc
      (∫ t in Ioi (0 : ℝ), u' t * v t) =
          ∫ t in Ioi (0 : ℝ),
            (x : ℂ) * complexKernel x lam α t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp [u', v, z, complexKernel]
        rw [Complex.ofReal_mul]
        ring
      _ = (x : ℂ) *
          ∫ t in Ioi (0 : ℝ), complexKernel x lam α t :=
        integral_const_mul
          (μ := volume.restrict (Ioi (0 : ℝ)))
          (x : ℂ) (complexKernel x lam α)
  change
    (∫ t in Ioi (0 : ℝ), u t * v' t) =
      -((x : ℂ) * complexValue x lam α)
  calc
    (∫ t in Ioi (0 : ℝ), u t * v' t) =
        -(∫ t in Ioi (0 : ℝ), u' t * v t) := by
      simpa using hparts
    _ = -((x : ℂ) * complexValue x lam α) := by
      rw [hint]

private theorem complexRate_hasDerivAt
    (lam α : ℝ) :
    HasDerivAt (complexRate lam) (rateDerivative lam α) α := by
  have hre :
      HasDerivAt
        (fun β : ℝ => ((-lam * Real.cos β : ℝ) : ℂ))
        ((lam * Real.sin α : ℝ) : ℂ) α := by
    convert
      ((Real.hasDerivAt_cos α).const_mul (-lam)).ofReal_comp
        using 1 <;> ring
  have him :
      HasDerivAt
        (fun β : ℝ =>
          ((lam * Real.sin β : ℝ) : ℂ) * Complex.I)
        (((lam * Real.cos α : ℝ) : ℂ) * Complex.I) α := by
    have hreal :
        HasDerivAt
          (fun β : ℝ => ((lam * Real.sin β : ℝ) : ℂ))
          ((lam * Real.cos α : ℝ) : ℂ) α := by
      convert
        ((Real.hasDerivAt_sin α).const_mul lam).ofReal_comp
          using 1 <;> ring
    exact hreal.mul_const Complex.I
  unfold complexRate rateDerivative
  exact hre.add him

private theorem angleDerivativeKernel_hasDerivAt
    (x lam α t : ℝ) :
    HasDerivAt (fun β : ℝ => complexKernel x lam β t)
      (angleDerivativeKernel x lam α t) α := by
  have hinner :
      HasDerivAt
        (fun β : ℝ => complexRate lam β * (t : ℂ))
        (rateDerivative lam α * (t : ℂ)) α :=
    (complexRate_hasDerivAt lam α).mul_const (t : ℂ)
  have hexp := hinner.cexp
  have hmul :=
    hexp.const_mul (((Real.rpow t (x - 1) : ℝ) : ℂ))
  simpa [complexKernel, angleDerivativeKernel, mul_assoc] using hmul

private theorem angleDerivativeKernel_continuousOn
    (x lam α : ℝ) :
    ContinuousOn (angleDerivativeKernel x lam α)
      (Ioi (0 : ℝ)) := by
  have hr :
      ContinuousOn (fun t : ℝ => Real.rpow t (x - 1))
        (Ioi (0 : ℝ)) :=
    continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt ht))
  have hrc :
      ContinuousOn
        (fun t : ℝ => ((Real.rpow t (x - 1) : ℝ) : ℂ))
        (Ioi (0 : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn hr
  unfold angleDerivativeKernel
  exact hrc.mul
    ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).mul
        (continuous_const.mul Complex.continuous_ofReal)).continuousOn

private theorem rateDerivative_norm_le
    (lam β : ℝ) (hlam : 0 < lam) :
    ‖rateDerivative lam β‖ ≤ 2 * lam := by
  unfold rateDerivative
  calc
    ‖((lam * Real.sin β : ℝ) : ℂ) +
        ((lam * Real.cos β : ℝ) : ℂ) * Complex.I‖ ≤
        ‖((lam * Real.sin β : ℝ) : ℂ)‖ +
          ‖((lam * Real.cos β : ℝ) : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |lam * Real.sin β| + |lam * Real.cos β| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    _ ≤ 2 * lam := by
      rw [abs_mul, abs_mul, abs_of_pos hlam]
      nlinarith [Real.abs_sin_le_one β, Real.abs_cos_le_one β]

private theorem rpow_mul_self
    (t x : ℝ) (ht : 0 < t) :
    Real.rpow t (x - 1) * t = Real.rpow t x := by
  calc
    Real.rpow t (x - 1) * t =
        Real.rpow t (x - 1) * Real.rpow t 1 := by simp
    _ = Real.rpow t ((x - 1) + 1) :=
      (Real.rpow_add ht (x - 1) 1).symm
    _ = Real.rpow t x := by ring_nf

private theorem derivativeMajorant_integrable
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    IntegrableOn (derivativeMajorant x lam α)
      (Ioi (0 : ℝ)) := by
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo hα
  have hc : 0 < lam * (Real.cos α / 2) := by
    positivity
  have h :=
    (gammaWeight_integrable (x + 1)
      (lam * (Real.cos α / 2)) (by linarith) hc).const_mul
        (2 * lam)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold derivativeMajorant
  congr 3
  · congr 1
    ring

private theorem angleDerivativeKernel_norm_le
    (x lam α β t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (hβ : Real.cos α / 2 < Real.cos β) :
    ‖angleDerivativeKernel x lam β t‖ ≤
      derivativeMajorant x lam α t := by
  have hrpow :
      0 < Real.rpow t (x - 1) :=
    Real.rpow_pos_of_pos ht (x - 1)
  have htNorm : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hre :
      ((complexRate lam β * (t : ℂ)).re) =
        -(lam * Real.cos β * t) := by
    unfold complexRate
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hexp :
      Real.exp (-(lam * Real.cos β * t)) ≤
        Real.exp (-(lam * (Real.cos α / 2) * t)) := by
    apply Real.exp_le_exp.mpr
    have hmul :
        lam * t * (Real.cos α / 2) <
          lam * t * Real.cos β :=
      mul_lt_mul_of_pos_left hβ (mul_pos hlam ht)
    nlinarith
  have hrate := rateDerivative_norm_le lam β hlam
  unfold angleDerivativeKernel derivativeMajorant
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hrpow, norm_mul, Complex.norm_exp, hre,
    norm_mul, htNorm]
  have hpow := rpow_mul_self t x ht
  calc
    Real.rpow t (x - 1) *
          (Real.exp (-(lam * Real.cos β * t)) *
            (‖rateDerivative lam β‖ * t)) ≤
        Real.rpow t (x - 1) *
          (Real.exp (-(lam * (Real.cos α / 2) * t)) *
            ((2 * lam) * t)) := by
      gcongr
    _ = 2 * lam *
          (Real.rpow t x *
            Real.exp (-(lam * (Real.cos α / 2) * t))) := by
      rw [show
        Real.rpow t (x - 1) *
            (Real.exp (-(lam * (Real.cos α / 2) * t)) *
              ((2 * lam) * t)) =
          (2 * lam) *
            ((Real.rpow t (x - 1) * t) *
              Real.exp (-(lam * (Real.cos α / 2) * t))) by ring,
        hpow]

private theorem rateDerivative_eq
    (lam β : ℝ) :
    rateDerivative lam β =
      -Complex.I * complexRate lam β := by
  have hdre :
      (rateDerivative lam β).re = lam * Real.sin β := by
    unfold rateDerivative
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hdim :
      (rateDerivative lam β).im = lam * Real.cos β := by
    unfold rateDerivative
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hzre :
      (complexRate lam β).re = -lam * Real.cos β := by
    unfold complexRate
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hzim :
      (complexRate lam β).im = lam * Real.sin β := by
    unfold complexRate
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  apply Complex.ext
  · rw [Complex.mul_re, hdre, hzre, hzim]
    norm_num
  · rw [Complex.mul_im, hdim, hzre, hzim]
    norm_num

private theorem angleDerivative_integral
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (∫ t in Ioi (0 : ℝ),
        angleDerivativeKernel x lam α t) =
      Complex.I * (x : ℂ) * complexValue x lam α := by
  let moment : ℝ → ℂ := fun t =>
    ((Real.rpow t x : ℝ) : ℂ) *
      (complexRate lam α *
        Complex.exp (complexRate lam α * t))
  have hpoint :
      (∫ t in Ioi (0 : ℝ),
          angleDerivativeKernel x lam α t) =
        -Complex.I * ∫ t in Ioi (0 : ℝ), moment t := by
    calc
      (∫ t in Ioi (0 : ℝ),
          angleDerivativeKernel x lam α t) =
          ∫ t in Ioi (0 : ℝ),
            -Complex.I * moment t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := ht
        have hpow := rpow_mul_self t x ht0
        unfold angleDerivativeKernel moment
        rw [rateDerivative_eq]
        have hpowC :
            ((Real.rpow t (x - 1) : ℝ) : ℂ) * (t : ℂ) =
              ((Real.rpow t x : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, hpow]
        calc
          ((Real.rpow t (x - 1) : ℝ) : ℂ) *
                (Complex.exp (complexRate lam α * (t : ℂ)) *
                  ((-Complex.I * complexRate lam α) * (t : ℂ))) =
              -Complex.I *
                ((((Real.rpow t (x - 1) : ℝ) : ℂ) * (t : ℂ)) *
                  (complexRate lam α *
                    Complex.exp (complexRate lam α * (t : ℂ)))) := by
            ring
          _ = -Complex.I *
                (((Real.rpow t x : ℝ) : ℂ) *
                  (complexRate lam α *
                    Complex.exp (complexRate lam α * (t : ℂ)))) := by
            rw [hpowC]
      _ = -Complex.I *
          ∫ t in Ioi (0 : ℝ), moment t :=
        integral_const_mul
          (μ := volume.restrict (Ioi (0 : ℝ)))
          (-Complex.I) moment
  have hmom :
      (∫ t in Ioi (0 : ℝ), moment t) =
        -((x : ℂ) * complexValue x lam α) := by
    simpa [moment] using
      complex_moment_relation x lam α hx hlam hα
  rw [hpoint, hmom]
  ring

private theorem complexValue_hasDerivAt
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (complexValue x lam)
      (Complex.I * (x : ℂ) * complexValue x lam α) α := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let s : Set ℝ :=
    Real.cos ⁻¹' Ioi (Real.cos α / 2)
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo hα
  have hs : s ∈ 𝓝 α := by
    dsimp [s]
    exact Real.continuous_cos.continuousAt
      (Ioi_mem_nhds (by linarith))
  have hFmeas :
      ∀ᶠ β in 𝓝 α,
        AEStronglyMeasurable (complexKernel x lam β) μ :=
    Filter.Eventually.of_forall fun β =>
      (complexKernel_continuousOn x lam β).aestronglyMeasurable
        measurableSet_Ioi
  have hFint :
      Integrable (complexKernel x lam α) μ := by
    exact complexKernel_integrable x lam α hx hlam hα
  have hF'meas :
      AEStronglyMeasurable
        (angleDerivativeKernel x lam α) μ :=
    (angleDerivativeKernel_continuousOn x lam α).aestronglyMeasurable
      measurableSet_Ioi
  have hbound :
      ∀ᵐ t ∂μ, ∀ β ∈ s,
        ‖angleDerivativeKernel x lam β t‖ ≤
          derivativeMajorant x lam α t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro β hβ
    exact angleDerivativeKernel_norm_le x lam α β t
      hlam ht hβ
  have hmajor :
      Integrable (derivativeMajorant x lam α) μ := by
    exact derivativeMajorant_integrable x lam α hx hlam hα
  have hdiff :
      ∀ᵐ t ∂μ, ∀ β ∈ s,
        HasDerivAt (fun γ : ℝ => complexKernel x lam γ t)
          (angleDerivativeKernel x lam β t) β := by
    filter_upwards with t
    intro β hβ
    exact angleDerivativeKernel_hasDerivAt x lam β t
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun β t => complexKernel x lam β t)
      (F' := fun β t => angleDerivativeKernel x lam β t)
      hs hFmeas hFint hF'meas hbound hmajor hdiff
  have hvalue :=
    angleDerivative_integral x lam α hx hlam hα
  rw [hvalue] at hmain
  simpa only [complexValue, μ] using hmain.2

private def rotatedValue (x lam α : ℝ) : ℂ :=
  Complex.exp
      (-(((x * α : ℝ) : ℂ) * Complex.I)) *
    complexValue x lam α

private theorem rotatedValue_hasDerivAt
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (rotatedValue x lam) 0 α := by
  have hreal :
      HasDerivAt
        (fun β : ℝ => ((x * β : ℝ) : ℂ))
        (x : ℂ) α := by
    convert
      ((hasDerivAt_id α).const_mul x).ofReal_comp using 1 <;>
        ring
  have hinner :
      HasDerivAt
        (fun β : ℝ =>
          -(((x * β : ℝ) : ℂ) * Complex.I))
        (-((x : ℂ) * Complex.I)) α :=
    (hreal.mul_const Complex.I).neg
  have hexp := hinner.cexp
  have hvalue :=
    complexValue_hasDerivAt x lam α hx hlam hα
  have hprod := hexp.mul hvalue
  convert hprod using 1
  ring

private theorem rotatedValue_eq_zero
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    rotatedValue x lam α = rotatedValue x lam 0 := by
  let s : Set ℝ :=
    Ioo (-(Real.pi / 2)) (Real.pi / 2)
  have hdiff :
      DifferentiableOn ℝ (rotatedValue x lam) s := by
    intro β hβ
    exact
      (rotatedValue_hasDerivAt x lam β hx hlam hβ).differentiableAt
        |>.differentiableWithinAt
  have hderiv :
      s.EqOn (deriv (rotatedValue x lam)) 0 := by
    intro β hβ
    exact (rotatedValue_hasDerivAt x lam β hx hlam hβ).deriv
  have h0 : (0 : ℝ) ∈ s := by
    dsimp [s]
    constructor <;> linarith [Real.pi_pos]
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero
      isPreconnected_Ioo hdiff hderiv hα h0

private theorem complexValue_zero
    (x lam : ℝ) (hx : 0 < x) (hlam : 0 < lam) :
    complexValue x lam 0 =
      ((Real.Gamma x / Real.rpow lam x : ℝ) : ℂ) := by
  have hα0 :
      (0 : ℝ) ∈
        Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hint :=
    complexKernel_integrable x lam 0 hx hlam hα0
  have hre :
      (∫ t in Ioi (0 : ℝ),
          (complexKernel x lam 0 t).re) =
        (∫ t in Ioi (0 : ℝ),
          complexKernel x lam 0 t).re := by
    simpa only [RCLike.re_to_complex] using
      (integral_re (𝕜 := ℂ) hint)
  have him :
      (∫ t in Ioi (0 : ℝ),
          (complexKernel x lam 0 t).im) =
        (∫ t in Ioi (0 : ℝ),
          complexKernel x lam 0 t).im := by
    simpa only [RCLike.im_to_complex] using
      (integral_im (𝕜 := ℂ) hint)
  apply Complex.ext
  · rw [Complex.ofReal_re]
    unfold complexValue
    rw [← hre]
    calc
      (∫ t in Ioi (0 : ℝ),
          (complexKernel x lam 0 t).re) =
          ∫ t in Ioi (0 : ℝ),
            Real.rpow t (x - 1) *
              Real.exp (-(lam * t)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [complexKernel, complexRate]
        left
        convert Complex.exp_ofReal_re (-(lam * t)) using 1 <;>
          push_cast <;> ring
      _ = (1 / lam) ^ x * Real.Gamma x :=
        Real.integral_rpow_mul_exp_neg_mul_Ioi hx hlam
      _ = Real.Gamma x / Real.rpow lam x := by
        rw [Real.div_rpow zero_le_one hlam.le x,
          Real.one_rpow]
        simp only [div_eq_mul_inv, one_mul]
        rw [Real.rpow_eq_pow]
        ring
  · rw [Complex.ofReal_im]
    unfold complexValue
    rw [← him]
    calc
      (∫ t in Ioi (0 : ℝ),
          (complexKernel x lam 0 t).im) =
          ∫ t in Ioi (0 : ℝ), (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [complexKernel, complexRate]
        right
        convert Complex.exp_ofReal_im (-(lam * t)) using 1 <;>
          push_cast <;> ring
      _ = 0 := by simp

private theorem complexValue_formula
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    complexValue x lam α =
      ((Real.Gamma x / Real.rpow lam x : ℝ) : ℂ) *
        Complex.exp
          ((((x * α : ℝ) : ℂ) * Complex.I)) := by
  let u : ℂ :=
    (((x * α : ℝ) : ℂ) * Complex.I)
  have hrot :
      Complex.exp (-u) * complexValue x lam α =
        complexValue x lam 0 := by
    simpa [rotatedValue, u] using
      rotatedValue_eq_zero x lam α hx hlam hα
  have hcancel :
      Complex.exp u * Complex.exp (-u) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    complexValue x lam α =
        (Complex.exp u * Complex.exp (-u)) *
          complexValue x lam α := by
      rw [hcancel, one_mul]
    _ = Complex.exp u *
          (Complex.exp (-u) * complexValue x lam α) := by
      ring
    _ = Complex.exp u * complexValue x lam 0 := by
      rw [hrot]
    _ = Complex.exp u *
          ((Real.Gamma x / Real.rpow lam x : ℝ) : ℂ) := by
      rw [complexValue_zero x lam hx hlam]
    _ = ((Real.Gamma x / Real.rpow lam x : ℝ) : ℂ) *
          Complex.exp
            ((((x * α : ℝ) : ℂ) * Complex.I)) := by
      dsimp [u]
      ring

private theorem complexValue_im
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (complexValue x lam α).im =
      Real.Gamma x / Real.rpow lam x *
        Real.sin (α * x) := by
  rw [complexValue_formula x lam α hx hlam hα,
    Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  rw [Complex.exp_ofReal_mul_I_im, mul_comm x α]

private theorem complexKernel_im
    (x lam α t : ℝ) :
    (complexKernel x lam α t).im =
      Real.rpow t (x - 1) *
        Real.exp (-(lam * t) * Real.cos α) *
          Real.sin (lam * t * Real.sin α) := by
  have hre :
      (complexRate lam α * (t : ℂ)).re =
        -(lam * t) * Real.cos α := by
    unfold complexRate
    simp only [Complex.mul_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him :
      (complexRate lam α * (t : ℂ)).im =
        lam * t * Real.sin α := by
    unfold complexRate
    simp only [Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  unfold complexKernel
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_im, hre, him]
  ring

private theorem realIntegral_eq_complexValue_im
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (∫ t in Ioi (0 : ℝ),
        Real.rpow t (x - 1) *
          Real.exp (-(lam * t) * Real.cos α) *
            Real.sin (lam * t * Real.sin α)) =
      (complexValue x lam α).im := by
  have hint :=
    complexKernel_integrable x lam α hx hlam hα
  have him :
      (∫ t in Ioi (0 : ℝ),
          (complexKernel x lam α t).im) =
        (complexValue x lam α).im := by
    unfold complexValue
    simpa only [RCLike.im_to_complex] using
      (integral_im (𝕜 := ℂ) hint)
  calc
    (∫ t in Ioi (0 : ℝ),
        Real.rpow t (x - 1) *
          Real.exp (-(lam * t) * Real.cos α) *
            Real.sin (lam * t * Real.sin α)) =
        ∫ t in Ioi (0 : ℝ),
          (complexKernel x lam α t).im := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (complexKernel_im x lam α t).symm
    _ = (complexValue x lam α).im := him

/-- Exercise 3878_2. -/
private theorem sine_setIntegral_formula
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    (∫ t in Ioi (0 : ℝ),
      Real.rpow t (x - 1) * Real.exp (-(lam * t) * Real.cos α) *
        Real.sin (lam * t * Real.sin α) ∂MeasureTheory.volume) =
      Real.Gamma x / Real.rpow lam x * Real.sin (α * x) := by
  have hα :
      α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨hα₀, hα₁⟩
  calc
    (∫ t in Ioi (0 : ℝ),
        Real.rpow t (x - 1) *
          Real.exp (-(lam * t) * Real.cos α) *
            Real.sin (lam * t * Real.sin α)) =
        (complexValue x lam α).im :=
      realIntegral_eq_complexValue_im x lam α hx hlam hα
    _ = Real.Gamma x / Real.rpow lam x *
          Real.sin (α * x) :=
      complexValue_im x lam α hx hlam hα

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
  rw [hs, csInf_singleton]

private theorem hasImproperIntegral_of_integrableOn
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    HasImproperIntegral 0 f (∫ t in Ioi (0 : ℝ), f t) := by
  unfold HasImproperIntegral
  exact intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id

private theorem improperIntegral_eq_setIntegral
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    improperIntegral 0 f = ∫ t in Ioi (0 : ℝ), f t :=
  improperIntegral_eq_of_hasImproperIntegral
    (hasImproperIntegral_of_integrableOn hf)

private theorem complexKernel_re
    (x lam α t : ℝ) :
    (complexKernel x lam α t).re =
      Real.rpow t (x - 1) *
        Real.exp (-(lam * t) * Real.cos α) *
          Real.cos (lam * t * Real.sin α) := by
  have hre :
      (complexRate lam α * (t : ℂ)).re =
        -(lam * t) * Real.cos α := by
    unfold complexRate
    simp only [Complex.mul_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him :
      (complexRate lam α * (t : ℂ)).im =
        lam * t * Real.sin α := by
    unfold complexRate
    simp only [Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  unfold complexKernel
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_re, hre, him]
  ring

private theorem complexValue_re
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (complexValue x lam α).re =
      Real.Gamma x / Real.rpow lam x *
        Real.cos (α * x) := by
  rw [complexValue_formula x lam α hx hlam hα,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [Complex.exp_ofReal_mul_I_re, mul_comm x α]

private theorem cosKernel_integrable
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    IntegrableOn (cosKernel lam x α) (Ioi (0 : ℝ)) := by
  have hcomplex :=
    complexKernel_integrable x lam α hx hlam ⟨hα₀, hα₁⟩
  have hre := hcomplex.re
  apply hre.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (complexKernel x lam α t).re = cosKernel lam x α t
  rw [complexKernel_re]
  rfl

private theorem sinKernel_integrable
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    IntegrableOn (sinKernel lam x α) (Ioi (0 : ℝ)) := by
  have hcomplex :=
    complexKernel_integrable x lam α hx hlam ⟨hα₀, hα₁⟩
  have him := hcomplex.im
  apply him.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (complexKernel x lam α t).im = sinKernel lam x α t
  rw [complexKernel_im]
  rfl

private theorem realIntegral_eq_complexValue_re
    (x lam α : ℝ) (hx : 0 < x) (hlam : 0 < lam)
    (hα : α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (∫ t in Ioi (0 : ℝ),
        Real.rpow t (x - 1) *
          Real.exp (-(lam * t) * Real.cos α) *
            Real.cos (lam * t * Real.sin α)) =
      (complexValue x lam α).re := by
  have hint :=
    complexKernel_integrable x lam α hx hlam hα
  have hre :
      (∫ t in Ioi (0 : ℝ),
          (complexKernel x lam α t).re) =
        (complexValue x lam α).re := by
    unfold complexValue
    simpa only [RCLike.re_to_complex] using
      (integral_re (𝕜 := ℂ) hint)
  calc
    (∫ t in Ioi (0 : ℝ),
        Real.rpow t (x - 1) *
          Real.exp (-(lam * t) * Real.cos α) *
            Real.cos (lam * t * Real.sin α)) =
        ∫ t in Ioi (0 : ℝ),
          (complexKernel x lam α t).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (complexKernel_re x lam α t).symm
    _ = (complexValue x lam α).re := hre

private theorem cos_setIntegral_formula
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    (∫ t in Ioi (0 : ℝ), cosKernel lam x α t) =
      Real.Gamma x / Real.rpow lam x * Real.cos (α * x) := by
  calc
    _ = (complexValue x lam α).re := by
      exact realIntegral_eq_complexValue_re x lam α hx hlam ⟨hα₀, hα₁⟩
    _ = _ := complexValue_re x lam α hx hlam ⟨hα₀, hα₁⟩

private theorem gammaWeight_setIntegral
    (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ),
        Real.rpow t (x - 1) * Real.exp (-(c * t))) =
      Real.Gamma x / Real.rpow c x := by
  change
    (∫ t in Ioi (0 : ℝ),
      t ^ (x - 1) * Real.exp (-(c * t))) =
      Real.Gamma x / c ^ x
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hx hc]
  rw [one_div, Real.inv_rpow hc.le]
  ring

private theorem baseKernel_integrable
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    IntegrableOn (baseKernel lam x α) (Ioi (0 : ℝ)) := by
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨hα₀, hα₁⟩
  have hc : 0 < lam * Real.cos α := mul_pos hlam hcos
  have h := gammaWeight_integrable x (lam * Real.cos α) hx hc
  apply h.congr
  filter_upwards with t
  unfold baseKernel
  congr 2
  ring

private theorem baseKernel_improper_formula
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    improperIntegral 0 (baseKernel lam x α) =
      Real.Gamma x / Real.rpow (lam * Real.cos α) x := by
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨hα₀, hα₁⟩
  have hc : 0 < lam * Real.cos α := mul_pos hlam hcos
  rw [improperIntegral_eq_setIntegral
    (baseKernel_integrable lam x α hlam hx hα₀ hα₁)]
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        Real.rpow t (x - 1) *
          Real.exp (-((lam * Real.cos α) * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      unfold baseKernel
      congr 2
      ring
    _ = _ := gammaWeight_setIntegral x (lam * Real.cos α) hx hc

private theorem standardGamma_improper_formula
    (x : ℝ) (hx : 0 < x) :
    improperIntegral 0
        (fun u => Real.rpow u (x - 1) * Real.exp (-u)) =
      Real.Gamma x := by
  have hint := gammaWeight_integrable x 1 hx zero_lt_one
  have heq :
      (fun u : ℝ => Real.rpow u (x - 1) * Real.exp (-u)) =
        fun u => Real.rpow u (x - 1) * Real.exp (-(1 * u)) := by
    funext u
    congr 2
    ring
  rw [heq, improperIntegral_eq_setIntegral hint,
    gammaWeight_setIntegral x 1 hx zero_lt_one]
  simp

private theorem I_formula
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    I lam x α =
      Real.Gamma x / Real.rpow lam x * Real.cos (α * x) := by
  unfold I
  rw [improperIntegral_eq_setIntegral
    (cosKernel_integrable lam x α hlam hx hα₀ hα₁)]
  exact cos_setIntegral_formula lam x α hlam hx hα₀ hα₁

private theorem I₁_formula
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    I₁ lam x α =
      Real.Gamma x / Real.rpow lam x * Real.sin (α * x) := by
  unfold I₁
  rw [improperIntegral_eq_setIntegral
    (sinKernel_integrable lam x α hlam hx hα₀ hα₁)]
  exact sine_setIntegral_formula x lam α hx hlam hα₀ hα₁

private theorem I_deriv_formula
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    deriv (I lam x) α =
      -(Real.Gamma x / Real.rpow lam x * x *
        Real.sin (α * x)) := by
  let A : ℝ := Real.Gamma x / Real.rpow lam x
  have heq :
      I lam x =ᶠ[nhds α] fun β => A * Real.cos (β * x) := by
    filter_upwards [Ioo_mem_nhds hα₀ hα₁] with β hβ
    exact I_formula lam x β hlam hx hβ.1 hβ.2
  have hinner :
      HasDerivAt (fun β : ℝ => β * x) x α := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (𝕜 := ℝ) α).mul_const x
  have hclosed :
      HasDerivAt (fun β : ℝ => A * Real.cos (β * x))
        (-(A * x * Real.sin (α * x))) α := by
    convert ((Real.hasDerivAt_cos (α * x)).comp α hinner).const_mul A
      using 1 <;> ring
  rw [heq.deriv_eq, hclosed.deriv]

private theorem I₁_deriv_formula
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    deriv (I₁ lam x) α =
      Real.Gamma x / Real.rpow lam x * x *
        Real.cos (α * x) := by
  let A : ℝ := Real.Gamma x / Real.rpow lam x
  have heq :
      I₁ lam x =ᶠ[nhds α] fun β => A * Real.sin (β * x) := by
    filter_upwards [Ioo_mem_nhds hα₀ hα₁] with β hβ
    exact I₁_formula lam x β hlam hx hβ.1 hβ.2
  have hinner :
      HasDerivAt (fun β : ℝ => β * x) x α := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (𝕜 := ℝ) α).mul_const x
  have hclosed :
      HasDerivAt (fun β : ℝ => A * Real.sin (β * x))
        (A * x * Real.cos (α * x)) α := by
    convert ((Real.hasDerivAt_sin (α * x)).comp α hinner).const_mul A
      using 1 <;> ring
  rw [heq.deriv_eq, hclosed.deriv]

private theorem I_second_deriv_formula
    (lam x α : ℝ) (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -(Real.pi / 2) < α) (hα₁ : α < Real.pi / 2) :
    deriv (deriv (I lam x)) α =
      -(Real.Gamma x / Real.rpow lam x * x ^ 2 *
        Real.cos (α * x)) := by
  let A : ℝ := Real.Gamma x / Real.rpow lam x
  have heq :
      deriv (I lam x) =ᶠ[nhds α]
        fun β => -(A * x * Real.sin (β * x)) := by
    filter_upwards [Ioo_mem_nhds hα₀ hα₁] with β hβ
    exact I_deriv_formula lam x β hlam hx hβ.1 hβ.2
  have hinner :
      HasDerivAt (fun β : ℝ => β * x) x α := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (𝕜 := ℝ) α).mul_const x
  have hclosed :
      HasDerivAt (fun β : ℝ => -(A * x * Real.sin (β * x)))
        (-(A * x ^ 2 * Real.cos (α * x))) α := by
    convert
      (((Real.hasDerivAt_sin (α * x)).comp α hinner).const_mul
        (A * x)).neg using 1 <;> ring
  rw [heq.deriv_eq, hclosed.deriv]

private theorem lowerAngle_normalize {α : ℝ}
    (h : -Real.pi / 2 < α) :
    -(Real.pi / 2) < α := by
  linarith

private theorem lowerAngle_denormalize {α : ℝ}
    (h : -(Real.pi / 2) < α) :
    -Real.pi / 2 < α := by
  linarith

theorem gap1 (lam x α t : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2)
    (ht : 0 < t) :
    |cosKernel lam x α t| ≤ baseKernel lam x α t := by
  have hbase :
      0 ≤ baseKernel lam x α t := by
    unfold baseKernel
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  unfold cosKernel
  rw [abs_mul, abs_of_nonneg hbase]
  calc
    baseKernel lam x α t * |Real.cos (lam * t * Real.sin α)| ≤
        baseKernel lam x α t * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hbase
    _ = baseKernel lam x α t := mul_one _

theorem gap2 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    improperIntegral 0 (baseKernel lam x α) =
      1 / Real.rpow (lam * Real.cos α) x *
        improperIntegral 0
          (fun u => Real.rpow u (x - 1) * Real.exp (-u)) := by
  rw [baseKernel_improper_formula lam x α hlam hx
      (lowerAngle_normalize hα₀) hα₁,
    standardGamma_improper_formula x hx]
  ring

theorem gap3 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    1 / Real.rpow (lam * Real.cos α) x *
        improperIntegral 0
          (fun u => Real.rpow u (x - 1) * Real.exp (-u)) =
      Real.Gamma x / Real.rpow (lam * Real.cos α) x := by
  rw [standardGamma_improper_formula x hx]
  ring

theorem gap4 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    0 < Real.rpow (lam * Real.cos α) x := by
  exact Real.rpow_pos_of_pos
    (mul_pos hlam
      (Real.cos_pos_of_mem_Ioo ⟨lowerAngle_normalize hα₀, hα₁⟩)) x

theorem gap5 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    HasImproperIntegral 0 (baseKernel lam x α)
      (Real.Gamma x / Real.rpow (lam * Real.cos α) x) := by
  have hhas :=
    hasImproperIntegral_of_integrableOn
      (baseKernel_integrable lam x α hlam hx
        (lowerAngle_normalize hα₀) hα₁)
  have heq :
      (∫ t in Ioi (0 : ℝ), baseKernel lam x α t) =
        Real.Gamma x / Real.rpow (lam * Real.cos α) x := by
    calc
      _ = improperIntegral 0 (baseKernel lam x α) :=
        (improperIntegral_eq_setIntegral
          (baseKernel_integrable lam x α hlam hx
            (lowerAngle_normalize hα₀) hα₁)).symm
      _ = _ := baseKernel_improper_formula lam x α hlam hx
        (lowerAngle_normalize hα₀) hα₁
  rw [heq] at hhas
  exact hhas

theorem gap6 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    ∃ L : ℝ, HasImproperIntegral 0 (cosKernel lam x α) L := by
  exact ⟨∫ t in Ioi (0 : ℝ), cosKernel lam x α t,
    hasImproperIntegral_of_integrableOn
      (cosKernel_integrable lam x α hlam hx
        (lowerAngle_normalize hα₀) hα₁)⟩

theorem gap7 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    ∃ L : ℝ, HasImproperIntegral 0 (sinKernel lam x α) L := by
  exact ⟨∫ t in Ioi (0 : ℝ), sinKernel lam x α t,
    hasImproperIntegral_of_integrableOn
      (sinKernel_integrable lam x α hlam hx
        (lowerAngle_normalize hα₀) hα₁)⟩

theorem gap8 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    deriv (I₁ lam x) α = x * I lam x α := by
  rw [I₁_deriv_formula lam x α hlam hx
      (lowerAngle_normalize hα₀) hα₁,
    I_formula lam x α hlam hx (lowerAngle_normalize hα₀) hα₁]
  ring

theorem gap9 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    deriv (deriv (I lam x)) α + x ^ 2 * I lam x α = 0 := by
  rw [I_second_deriv_formula lam x α hlam hx
      (lowerAngle_normalize hα₀) hα₁,
    I_formula lam x α hlam hx (lowerAngle_normalize hα₀) hα₁]
  ring

theorem gap10 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    ∃ C₁ C₂ : ℝ, ∀ β ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2),
      I lam x β = C₁ * Real.cos (β * x) + C₂ * Real.sin (β * x) := by
  refine ⟨Real.Gamma x / Real.rpow lam x, 0, ?_⟩
  intro β hβ
  rw [I_formula lam x β hlam hx
    (lowerAngle_normalize hβ.1) hβ.2]
  ring

theorem gap11 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    ∃ C₁ : ℝ, C₁ = I lam x 0 := by
  exact ⟨I lam x 0, rfl⟩

theorem gap12 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    I lam x 0 =
      improperIntegral 0
        (fun t => Real.rpow t (x - 1) * Real.exp (-(lam * t))) := by
  unfold I cosKernel baseKernel
  congr 2
  funext t
  simp

theorem gap13 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    improperIntegral 0
        (fun t => Real.rpow t (x - 1) * Real.exp (-(lam * t))) =
      Real.Gamma x / Real.rpow lam x := by
  have hint := gammaWeight_integrable x lam hx hlam
  rw [improperIntegral_eq_setIntegral hint,
    gammaWeight_setIntegral x lam hx hlam]

theorem gap14 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    ∃ C₁ : ℝ, C₁ = Real.Gamma x / Real.rpow lam x := by
  exact ⟨Real.Gamma x / Real.rpow lam x, rfl⟩

theorem gap15 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    deriv (I lam x) 0 = -x * I₁ lam x 0 := by
  rw [I_deriv_formula lam x 0 hlam hx
      (by nlinarith [Real.pi_pos]) (by positivity),
    I₁_formula lam x 0 hlam hx
      (by nlinarith [Real.pi_pos]) (by positivity)]
  simp

theorem gap16 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    deriv (I lam x) 0 = evalAt 0 (deriv (I lam x)) := by
  rfl

theorem gap17 (lam x α C₁ C₂ : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2)
    (hsol : ∀ β ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2),
      I lam x β = C₁ * Real.cos (β * x) + C₂ * Real.sin (β * x)) :
    evalAt 0 (deriv (I lam x)) =
      evalAt 0
        (fun β =>
          -C₁ * x * Real.sin (β * x) +
            C₂ * x * Real.cos (β * x)) := by
  have hzero :
      (0 : ℝ) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith [Real.pi_pos]
    · positivity
  have heq :
      I lam x =ᶠ[nhds 0]
        fun β => C₁ * Real.cos (β * x) + C₂ * Real.sin (β * x) := by
    filter_upwards [Ioo_mem_nhds hzero.1 hzero.2] with β hβ
    exact hsol β ⟨lowerAngle_denormalize hβ.1, hβ.2⟩
  have hinner :
      HasDerivAt (fun β : ℝ => β * x) x 0 := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (𝕜 := ℝ) 0).mul_const x
  have hcos :=
    ((Real.hasDerivAt_cos (0 * x)).comp 0 hinner).const_mul C₁
  have hsin :=
    ((Real.hasDerivAt_sin (0 * x)).comp 0 hinner).const_mul C₂
  have hclosed :
      HasDerivAt
        (fun β => C₁ * Real.cos (β * x) + C₂ * Real.sin (β * x))
        (-C₁ * x * Real.sin (0 * x) +
          C₂ * x * Real.cos (0 * x)) 0 := by
    convert hcos.add hsin using 1 <;> ring
  unfold evalAt
  rw [heq.deriv_eq, hclosed.deriv]

theorem gap18 (x C₁ C₂ : ℝ) :
    evalAt 0
        (fun β =>
          -C₁ * x * Real.sin (β * x) +
            C₂ * x * Real.cos (β * x)) =
      C₂ * x := by
  simp [evalAt]

theorem gap19 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    ∃ C₂ : ℝ, deriv (I lam x) 0 = C₂ * x := by
  refine ⟨deriv (I lam x) 0 / x, ?_⟩
  field_simp [hx.ne']

theorem gap20 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    I₁ lam x 0 = 0 := by
  rw [I₁_formula lam x 0 hlam hx
    (by nlinarith [Real.pi_pos]) (by positivity)]
  simp

theorem gap21 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    ∃ C₂ : ℝ, C₂ = 0 := by
  exact ⟨0, rfl⟩

theorem gap22 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    I₁ lam x α = -(1 / x) * deriv (I lam x) α := by
  rw [I₁_formula lam x α hlam hx
      (lowerAngle_normalize hα₀) hα₁,
    I_deriv_formula lam x α hlam hx
      (lowerAngle_normalize hα₀) hα₁]
  field_simp [hx.ne']

theorem gap23 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    -(1 / x) * deriv (I lam x) α =
      Real.Gamma x / Real.rpow lam x * Real.sin (α * x) := by
  rw [I_deriv_formula lam x α hlam hx
    (lowerAngle_normalize hα₀) hα₁]
  field_simp [hx.ne']

theorem gap24 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    I₁ lam x α =
      Real.Gamma x / Real.rpow lam x * Real.sin (α * x) := by
  exact I₁_formula lam x α hlam hx
    (lowerAngle_normalize hα₀) hα₁

theorem gap25 (lam x α : ℝ)
    (hlam : 0 < lam) (hx : 0 < x)
    (hα₀ : -Real.pi / 2 < α) (hα₁ : α < Real.pi / 2) :
    improperIntegral 0 (sinKernel lam x α) =
      Real.Gamma x / Real.rpow lam x * Real.sin (α * x) := by
  exact gap24 lam x α hlam hx hα₀ hα₁

end

end ProofGap.Exercise3878_2
