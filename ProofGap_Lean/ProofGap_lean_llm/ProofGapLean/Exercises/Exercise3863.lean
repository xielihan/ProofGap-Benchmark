import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3863

noncomputable section

open MeasureTheory Set
open Filter Asymptotics
open scoped Interval Topology

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def betaFn (p q : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (p - 1) * Real.rpow (1 - t) (q - 1)

def kernel (p x : ℝ) : ℝ :=
  Real.rpow x (p - 1) / (1 + x)

def logKernel (p x : ℝ) : ℝ :=
  Real.rpow x (p - 1) * Real.log x / (1 + x)

private def mellinBase (x : ℝ) : ℂ :=
  ((1 / (1 + x) : ℝ) : ℂ)

private def betaKernel (u v t : ℝ) : ℝ :=
  Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)

private theorem mellinBase_continuousOn :
    ContinuousOn mellinBase (Ioi (0 : ℝ)) := by
  intro x hx
  change 0 < x at hx
  unfold mellinBase
  apply ContinuousAt.continuousWithinAt
  exact Complex.continuous_ofReal.continuousAt.comp
    (continuousAt_const.div
      (continuousAt_const.add continuousAt_id)
      (by linarith [hx]))

private theorem mellinBase_top :
    mellinBase =O[atTop] (fun x : ℝ => x ^ (-(1 : ℝ))) := by
  apply IsBigO.of_bound' 
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hden : 0 < 1 + x := by linarith
  simp only [mellinBase, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hden), Real.rpow_neg_one,
    abs_of_pos (inv_pos.mpr hx0)]
  rw [one_div, inv_le_inv₀ hden hx0]
  linarith

private theorem mellinBase_bot :
    mellinBase =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  have hden : 0 < 1 + x := by linarith
  simp only [mellinBase, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hden), neg_zero, Real.rpow_zero, norm_one]
  calc
    1 / (1 + x) ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ = 1 := by norm_num

private theorem mellinDeriv (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    MellinConvergent (fun t => Real.log t • mellinBase t) (p : ℂ) ∧
      HasDerivAt (mellin mellinBase)
        (mellin (fun t => Real.log t • mellinBase t) (p : ℂ)) (p : ℂ) := by
  exact mellin_hasDerivAt_of_isBigO_rpow
    (mellinBase_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    mellinBase_top (by simpa using hp1) mellinBase_bot (by simpa using hp)

private theorem mellinBase_ofReal (q : ℝ) :
    mellin mellinBase (q : ℂ) =
      (((∫ x in Ioi (0 : ℝ), kernel q x ∂volume) : ℝ) : ℂ) := by
  rw [mellin]
  calc
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((q : ℂ) - 1) • mellinBase x ∂volume) =
        ∫ x in Ioi (0 : ℝ), ((kernel q x : ℝ) : ℂ) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      simp only [mellinBase, kernel, smul_eq_mul, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_add]
      have hpow :
          (x : ℂ) ^ ((q : ℂ) - 1) = ((Real.rpow x (q - 1) : ℝ) : ℂ) := by
        calc
          (x : ℂ) ^ ((q : ℂ) - 1) =
              (x : ℂ) ^ ((q - 1 : ℝ) : ℂ) := by
            congr 1
            norm_num
          _ = ((Real.rpow x (q - 1) : ℝ) : ℂ) :=
            (Complex.ofReal_cpow hx.le (q - 1)).symm
      rw [hpow]
      simp only [div_eq_mul_inv]
      ring
    _ = _ := integral_ofReal

private theorem mellinLog_ofReal (q : ℝ) :
    mellin (fun t => Real.log t • mellinBase t) (q : ℂ) =
      (((∫ x in Ioi (0 : ℝ), logKernel q x ∂volume) : ℝ) : ℂ) := by
  rw [mellin]
  calc
    (∫ x in Ioi (0 : ℝ),
        (x : ℂ) ^ ((q : ℂ) - 1) • Real.log x • mellinBase x ∂volume) =
        ∫ x in Ioi (0 : ℝ), ((logKernel q x : ℝ) : ℂ) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      simp only [mellinBase, logKernel, smul_eq_mul, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_mul]
      have hpow :
          (x : ℂ) ^ ((q : ℂ) - 1) = ((Real.rpow x (q - 1) : ℝ) : ℂ) := by
        calc
          (x : ℂ) ^ ((q : ℂ) - 1) =
              (x : ℂ) ^ ((q - 1 : ℝ) : ℂ) := by
            congr 1
            norm_num
          _ = ((Real.rpow x (q - 1) : ℝ) : ℂ) :=
            (Complex.ofReal_cpow hx.le (q - 1)).symm
      rw [hpow]
      simp only [Complex.real_smul, div_eq_mul_inv]
      ring
    _ = _ := integral_ofReal

private theorem betaPrime_substitution_logKernel
    {a b t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) *
        ((t / (1 - t)).rpow (a - 1) /
          (1 + t / (1 - t)).rpow (a + b)) =
      betaKernel a b t := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hfrac : 1 + t / (1 - t) = 1 / (1 - t) := by
    field_simp [ht1.ne']
    ring
  unfold betaKernel
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow ht0.le ht1.le, hfrac,
    Real.div_rpow zero_le_one ht1.le, Real.one_rpow]
  have hpow : (1 - t) ^ (2 : ℕ) = Real.rpow (1 - t) (2 : ℝ) :=
    (Real.rpow_natCast (1 - t) 2).symm
  rw [hpow]
  have hne1 : Real.rpow (1 - t) (a - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne2 : Real.rpow (1 - t) (a + b) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne3 : Real.rpow (1 - t) (2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  field_simp [hne1, hne2, hne3]
  calc
    Real.rpow (1 - t) (a + b) =
        Real.rpow (1 - t) (((2 : ℝ) + (a - 1)) + (b - 1)) := by
      congr 1
      ring
    _ = Real.rpow (1 - t) ((2 : ℝ) + (a - 1)) *
        Real.rpow (1 - t) (b - 1) :=
      Real.rpow_add ht1 _ _
    _ = Real.rpow (1 - t) (2 : ℝ) *
        Real.rpow (1 - t) (a - 1) *
        Real.rpow (1 - t) (b - 1) := by
      congr 1
      exact Real.rpow_add ht1 _ _

private theorem canonical_transformed
    {q t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) * kernel q (t / (1 - t)) =
      betaKernel q (1 - q) t := by
  have h := betaPrime_substitution_logKernel
    (a := q) (b := 1 - q) ht
  simpa [kernel] using h

private theorem ofReal_beta_setIntegral
    {u v : ℝ} :
    (((∫ t in Ioo (0 : ℝ) 1, betaKernel u v t ∂volume) : ℝ) : ℂ) =
      Complex.betaIntegral (u : ℂ) (v : ℂ) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    (((∫ t in Ioo (0 : ℝ) 1, betaKernel u v t) : ℝ) : ℂ) =
        ∫ t in Ioo (0 : ℝ) 1, ((betaKernel u v t : ℝ) : ℂ) :=
      integral_ofReal.symm
    _ = _ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp [betaKernel]
      rw [Complex.ofReal_mul]
      congr 1
      · calc
          ((t.rpow (u - 1) : ℝ) : ℂ) = (t : ℂ) ^ ((u - 1 : ℝ) : ℂ) :=
            Complex.ofReal_cpow ht.1.le (u - 1)
          _ = (t : ℂ) ^ ((u : ℂ) - 1) := by push_cast; rfl
      · calc
          (((1 - t).rpow (v - 1) : ℝ) : ℂ) =
              ((1 - t : ℝ) : ℂ) ^ ((v - 1 : ℝ) : ℂ) :=
            Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le) (v - 1)
          _ = (1 - (t : ℂ)) ^ ((v : ℂ) - 1) := by push_cast; rfl

private theorem beta_setIntegral_eq_gamma
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t in Ioo (0 : ℝ) 1, betaKernel u v t ∂volume) =
      Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [ofReal_beta_setIntegral,
    Complex.betaIntegral_eq_Gamma_mul_div (u := (u : ℂ)) (v := (v : ℂ))
      (by simpa) (by simpa)]
  simp only [← Complex.Gamma_ofReal, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add]

private theorem canonical_integral (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    (∫ x in Ioi (0 : ℝ), kernel q x ∂volume) =
      Real.pi / Real.sin (q * Real.pi) := by
  let f : ℝ → ℝ := fun t => t / (1 - t)
  let f' : ℝ → ℝ := fun t => 1 / (1 - t) ^ 2
  have hf' :
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivWithinAt f (f' t) (Ioo (0 : ℝ) 1) t := by
    intro t ht
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    have hdenDeriv : HasDerivAt (fun y : ℝ => 1 - y) (-1) t := by
      simpa only [Pi.sub_apply, Pi.one_apply, id_eq, zero_sub] using
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
    have hne : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
    convert (hasDerivAt_id t).div hdenDeriv hne using 1
    simp only [id_eq]
    field_simp [hne]
    ring
  have hinj : Set.InjOn f (Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    dsimp [f] at hab
    have ha0 : 1 - a ≠ 0 := (sub_pos.mpr ha.2).ne'
    have hb0 : 1 - b ≠ 0 := (sub_pos.mpr hb.2).ne'
    field_simp [ha0, hb0] at hab
    linarith
  have himage : f '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos ht.1 (sub_pos.mpr ht.2)
    · intro hx
      have hx' : 0 < x := hx
      have hden : 0 < 1 + x := by linarith
      refine ⟨x / (1 + x), ?_, ?_⟩
      · constructor
        · exact div_pos hx hden
        · exact (div_lt_one hden).2 (by linarith)
      · dsimp [f]
        field_simp [hden.ne']
        ring
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hf' hinj (kernel q)
  rw [himage] at hchange
  have hbeta :
      (∫ x in Ioi (0 : ℝ), kernel q x ∂volume) =
        ∫ t in Ioo (0 : ℝ) 1, betaKernel q (1 - q) t ∂volume := by
    rw [hchange]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [f, f']
    rw [abs_of_pos
      (one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne')))]
    exact canonical_transformed ht
  rw [hbeta, beta_setIntegral_eq_gamma hq (by linarith)]
  have href := Real.Gamma_mul_Gamma_one_sub q
  rw [show q + (1 - q) = 1 by ring, Real.Gamma_one, div_one]
  simpa only [mul_comm] using href

private theorem closed_hasDerivAt
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun r : ℝ => Real.pi / Real.sin (r * Real.pi))
      (-(Real.pi ^ 2 * Real.cos (q * Real.pi)) /
        Real.sin (q * Real.pi) ^ 2) q := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hang0 : 0 < q * Real.pi := mul_pos hq hpi
  have hang1 : q * Real.pi < Real.pi := by
    nlinarith
  have hsin : Real.sin (q * Real.pi) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hang0 hang1).ne'
  have harg :
      HasDerivAt (fun r : ℝ => r * Real.pi) Real.pi q := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id q).mul_const Real.pi
  have hden :=
    (Real.hasDerivAt_sin (q * Real.pi)).comp q harg
  have h :=
    (hasDerivAt_const q Real.pi).div hden hsin
  simp only [Function.comp_apply] at h
  convert h using 1
  ring

private theorem logIntegral_formula
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ x in Ioi (0 : ℝ), logKernel p x ∂volume) =
      -(Real.pi ^ 2 * Real.cos (p * Real.pi)) /
        Real.sin (p * Real.pi) ^ 2 := by
  have hM :=
    (mellinDeriv p hp hp1).2.comp_ofReal
  rw [mellinLog_ofReal] at hM
  have heq :
      (fun q : ℝ =>
        ((Real.pi / Real.sin (q * Real.pi) : ℝ) : ℂ)) =ᶠ[𝓝 p]
        (fun q : ℝ => mellin mellinBase (q : ℂ)) := by
    filter_upwards [Ioo_mem_nhds hp hp1] with q hq
    rw [mellinBase_ofReal, canonical_integral q hq.1 hq.2]
  have hclosed :
      HasDerivAt
        (fun q : ℝ =>
          ((Real.pi / Real.sin (q * Real.pi) : ℝ) : ℂ))
        (((∫ x in Ioi (0 : ℝ), logKernel p x ∂volume) : ℝ) : ℂ) p :=
    hM.congr_of_eventuallyEq heq
  have hexplicit :=
    (closed_hasDerivAt p hp hp1).ofReal_comp
  have hderiv := hclosed.unique hexplicit
  exact Complex.ofReal_injective hderiv

private theorem logKernel_integrable_of
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (logKernel p) (Ioi (0 : ℝ)) volume := by
  have hc := (mellinDeriv p hp hp1).1
  unfold MellinConvergent at hc
  have hcoe :
      IntegrableOn (fun x : ℝ => ((logKernel p x : ℝ) : ℂ))
        (Ioi (0 : ℝ)) volume := by
    apply hc.congr_fun
    · intro x hx
      change 0 < x at hx
      simp only [mellinBase, logKernel, smul_eq_mul, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_mul]
      have hpow :
          (x : ℂ) ^ (((p : ℂ) - 1)) =
            ((Real.rpow x (p - 1) : ℝ) : ℂ) := by
        calc
          (x : ℂ) ^ ((p : ℂ) - 1) =
              (x : ℂ) ^ ((p - 1 : ℝ) : ℂ) := by
            congr 1
            norm_num
          _ = ((Real.rpow x (p - 1) : ℝ) : ℂ) :=
            (Complex.ofReal_cpow hx.le (p - 1)).symm
      rw [hpow]
      simp only [Complex.real_smul, div_eq_mul_inv]
      ring
    · exact measurableSet_Ioi
  simpa using hcoe.re

private theorem rpow_aestronglyMeasurable_on
    (s : ℝ) (a b : ℝ) (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun x : ℝ => Real.rpow x s)
      (volume.restrict (Ioo a b)) := by
  apply ContinuousOn.aestronglyMeasurable
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    exact Real.continuousAt_rpow_const x s
      (Or.inl (by
        have : 0 < x := ha.trans_lt hx.1
        exact this.ne'))
  · exact measurableSet_Ioo

private theorem rpow_aestronglyMeasurable_Ioi
    (s a : ℝ) (ha : 0 ≤ a) :
    AEStronglyMeasurable (fun x : ℝ => Real.rpow x s)
      (volume.restrict (Ioi a)) := by
  apply ContinuousOn.aestronglyMeasurable
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    exact Real.continuousAt_rpow_const x s
      (Or.inl (by
        have : 0 < x := ha.trans_lt hx
        exact this.ne'))
  · exact measurableSet_Ioi

private theorem logKernel_integrable_iff (p : ℝ) :
    IntegrableOn (logKernel p) (Ioi (0 : ℝ)) volume ↔
      0 < p ∧ p < 1 := by
  constructor
  · intro h
    have hexpNeg : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
    have hsmall :
        IntegrableOn (logKernel p) (Ioo (0 : ℝ) (Real.exp (-1))) volume :=
      h.mono_set (by
        intro x hx
        exact hx.1)
    have hsmallMajor :
        IntegrableOn (fun x : ℝ => 2 * ‖logKernel p x‖)
          (Ioo (0 : ℝ) (Real.exp (-1))) volume :=
      hsmall.norm.const_mul 2
    have hpowSmall :
        IntegrableOn (fun x : ℝ => Real.rpow x (p - 1))
          (Ioo (0 : ℝ) (Real.exp (-1))) volume := by
      refine hsmallMajor.mono'
        (rpow_aestronglyMeasurable_on (p - 1) 0 (Real.exp (-1)) le_rfl) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx0 : 0 < x := hx.1
      have hxe : x < Real.exp (-1) := hx.2
      have hlog : Real.log x < -1 := by
        rw [Real.log_lt_iff_lt_exp hx0]
        exact hxe
      have hexpLtOne : Real.exp (-1 : ℝ) < 1 := by
        rw [← Real.exp_zero, Real.exp_lt_exp]
        norm_num
      have hx1 : x < 1 := hxe.trans hexpLtOne
      have hden : 0 < 1 + x := by linarith
      have hdenLt : 1 + x < 2 := by linarith
      have hrpow : 0 < Real.rpow x (p - 1) :=
        Real.rpow_pos_of_pos hx0 _
      rw [Real.norm_eq_abs, abs_of_pos hrpow]
      simp only [logKernel, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos hrpow, abs_of_neg (by linarith : Real.log x < 0),
        abs_of_pos hden]
      rw [← mul_div_assoc, le_div_iff₀ hden]
      nlinarith [mul_pos hrpow (by linarith : 0 < -Real.log x - 1)]
    have hpExp :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hexpNeg).1 hpowSmall
    have hexpPos : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
    have htail :
        IntegrableOn (logKernel p) (Ioi (Real.exp 1)) volume :=
      h.mono_set (by
        intro x hx
        exact (hexpPos.trans hx))
    have htailMajor :
        IntegrableOn (fun x : ℝ => 2 * ‖logKernel p x‖)
          (Ioi (Real.exp 1)) volume :=
      htail.norm.const_mul 2
    have hpowTail :
        IntegrableOn (fun x : ℝ => Real.rpow x (p - 2))
          (Ioi (Real.exp 1)) volume := by
      refine htailMajor.mono'
        (rpow_aestronglyMeasurable_Ioi (p - 2) (Real.exp 1) hexpPos.le) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hexpOne : 1 < Real.exp (1 : ℝ) := by
        rw [← Real.exp_zero, Real.exp_lt_exp]
        norm_num
      have hx1 : 1 < x := hexpOne.trans hx
      have hx0 : 0 < x := zero_lt_one.trans hx1
      have hlog : 1 < Real.log x := by
        rw [Real.lt_log_iff_exp_lt hx0]
        exact hx
      have hden : 0 < 1 + x := by linarith
      have hdenLt : 1 + x < 2 * x := by linarith
      have hrpow : 0 < Real.rpow x (p - 2) :=
        Real.rpow_pos_of_pos hx0 _
      have hstep :
          Real.rpow x (p - 1) = Real.rpow x (p - 2) * x := by
        calc
          Real.rpow x (p - 1) = Real.rpow x ((p - 2) + 1) := by
            congr 1
            ring
          _ = Real.rpow x (p - 2) * Real.rpow x 1 :=
            Real.rpow_add hx0 _ _
          _ = Real.rpow x (p - 2) * x := by
            rw [show Real.rpow x (1 : ℝ) = x from Real.rpow_one x]
      rw [Real.norm_eq_abs, abs_of_pos hrpow]
      simp only [logKernel, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos (by linarith : 0 < Real.log x), abs_of_pos hden]
      rw [hstep, abs_of_pos (mul_pos hrpow hx0), ← mul_div_assoc,
        le_div_iff₀ hden]
      nlinarith [mul_pos (mul_pos hrpow hx0)
        (by linarith : 0 < Real.log x - 1)]
    have hpTail :=
      (integrableOn_Ioi_rpow_iff hexpPos).1 hpowTail
    constructor <;> linarith
  · rintro ⟨hp, hp1⟩
    exact logKernel_integrable_of p hp hp1

private theorem kernel_integrable_of
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (kernel p) (Ioi (0 : ℝ)) volume := by
  have hc : MellinConvergent mellinBase (p : ℂ) :=
    mellinConvergent_of_isBigO_rpow
      (mellinBase_continuousOn.locallyIntegrableOn measurableSet_Ioi)
      mellinBase_top (by simpa using hp1) mellinBase_bot (by simpa using hp)
  have hcoe :
      IntegrableOn (fun x : ℝ => ((kernel p x : ℝ) : ℂ))
        (Ioi (0 : ℝ)) volume := by
    apply hc.congr_fun
    · intro x hx
      change 0 < x at hx
      simp only [mellinBase, kernel, smul_eq_mul, Complex.ofReal_div,
        Complex.ofReal_one, Complex.ofReal_add]
      have hpow :
          (x : ℂ) ^ (((p : ℂ) - 1)) =
            ((Real.rpow x (p - 1) : ℝ) : ℂ) := by
        calc
          (x : ℂ) ^ ((p : ℂ) - 1) =
              (x : ℂ) ^ ((p - 1 : ℝ) : ℂ) := by
            congr 1
            norm_num
          _ = ((Real.rpow x (p - 1) : ℝ) : ℂ) :=
            (Complex.ofReal_cpow hx.le (p - 1)).symm
      rw [hpow]
      simp only [div_eq_mul_inv]
      ring
    · exact measurableSet_Ioi
  simpa using hcoe.re

private theorem improperIntegral_eq_of_has
    {a : ℝ} {f : ℝ → ℝ} {L : ℝ}
    (h : HasImproperIntegral a f L) :
    improperIntegral a f = L := by
  unfold improperIntegral
  have hset : {K : ℝ | HasImproperIntegral a f K} = {L} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hK
      exact tendsto_nhds_unique hK h
    · rintro rfl
      exact h
  rw [hset]
  exact csInf_singleton L

private theorem improperIntegral_eq_setIntegral
    {a : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi a) volume) :
    improperIntegral a f = ∫ x in Ioi a, f x ∂volume :=
  improperIntegral_eq_of_has
    (intervalIntegral_tendsto_integral_Ioi a hf tendsto_id)

private theorem betaFn_closed
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    betaFn p (1 - p) = Real.pi / Real.sin (p * Real.pi) := by
  rw [betaFn, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo]
  change (∫ t in Ioo (0 : ℝ) 1, betaKernel p (1 - p) t ∂volume) =
    Real.pi / Real.sin (p * Real.pi)
  rw [beta_setIntegral_eq_gamma hp (by linarith),
    show p + (1 - p) = 1 by ring, Real.Gamma_one, div_one]
  simpa only [mul_comm] using Real.Gamma_mul_Gamma_one_sub p

private theorem deriv_kernel_eq_logKernel
    (p x : ℝ) (hx : 0 < x) :
    deriv (fun q => kernel q x) p = logKernel p x := by
  have hpow :
      HasDerivAt (fun q : ℝ => Real.rpow x (q - 1))
        (Real.rpow x (p - 1) * Real.log x) p := by
    convert ((hasDerivAt_id p).sub_const 1).const_rpow hx using 1 <;>
      simp only [id_eq]
    rw [mul_comm]
    simp
  have h := hpow.div_const (1 + x)
  exact h.deriv

private theorem improperIntegral_deriv_kernel
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    improperIntegral 0
        (fun x => deriv (fun q => kernel q x) p) =
      improperIntegral 0 (logKernel p) := by
  have hlog := logKernel_integrable_of p hp hp1
  rw [improperIntegral_eq_setIntegral hlog]
  apply improperIntegral_eq_of_has
  have heq :
      (fun b : ℝ =>
          ∫ x in (0 : ℝ)..b, deriv (fun q => kernel q x) p) =ᶠ[atTop]
        (fun b : ℝ => ∫ x in (0 : ℝ)..b, logKernel p x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro x hxmem
    rw [Set.uIoc_of_le hb] at hxmem
    exact deriv_kernel_eq_logKernel p x hxmem.1
  unfold HasImproperIntegral
  exact (intervalIntegral_tendsto_integral_Ioi 0 hlog tendsto_id).congr' heq.symm

theorem gap1 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    betaFn p (1 - p) = improperIntegral 0 (kernel p) := by
  rw [betaFn_closed p hp hp1,
    improperIntegral_eq_setIntegral (kernel_integrable_of p hp hp1),
    canonical_integral p hp hp1]

theorem gap2 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    improperIntegral 0 (logKernel p) =
      improperIntegral 0
        (fun x => deriv (fun q => kernel q x) p) := by
  exact (improperIntegral_deriv_kernel p hp hp1).symm

theorem gap3 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    improperIntegral 0 (logKernel p) =
      (∫ x in (0 : ℝ)..1, logKernel p x) +
        improperIntegral 1 (logKernel p) := by
  have hlog := logKernel_integrable_of p hp hp1
  have hleft : IntegrableOn (logKernel p) (Ioc (0 : ℝ) 1) volume :=
    hlog.mono_set (fun x hx => hx.1)
  have hright : IntegrableOn (logKernel p) (Ioi (1 : ℝ)) volume :=
    hlog.mono_set (by
      intro x hx
      change 1 < x at hx
      exact zero_lt_one.trans hx)
  rw [improperIntegral_eq_setIntegral hlog,
    improperIntegral_eq_setIntegral hright,
    intervalIntegral.integral_of_le (by norm_num)]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact setIntegral_union
    (Set.disjoint_left.2 (by
      intro x hxleft hxright
      exact (not_lt_of_ge hxleft.2) hxright))
    measurableSet_Ioi hleft hright

theorem gap4 (p p₀ p₁ x : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    |logKernel p x| ≤
      Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2.le
  have hden : 0 < 1 + x := by linarith
  have hpow :
      Real.rpow x (p - 1) ≤ Real.rpow x (p₀ - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
  have habspow :
      |Real.rpow x (p - 1)| = Real.rpow x (p - 1) :=
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)
  have habsden : |1 + x| = 1 + x := abs_of_pos hden
  rw [logKernel, abs_div, abs_mul, habspow, habsden]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)) hden.le

theorem gap5 (p p₀ p₁ : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    IntervalIntegrable
      (fun x => Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x))
      volume (0 : ℝ) 1 := by
  have hp₀1 : p₀ < 1 := lt_of_le_of_lt h₀p (hpp₁.trans_lt hp₁)
  have hlog := logKernel_integrable_of p₀ hp₀ hp₀1
  have hneg :
      IntegrableOn (fun x => -logKernel p₀ x) (Ioi (0 : ℝ)) volume :=
    hlog.neg
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)]
  refine (hneg.mono_set (fun x hx => hx.1)).congr_fun ?_ measurableSet_Ioc
  intro x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2
  change -logKernel p₀ x =
    Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x)
  rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1)]
  simp only [logKernel]
  ring

private theorem zero_weight_eq
    (p₀ x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Real.rpow x (1 - p₀ / 2) *
          (Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x)) =
      (-Real.rpow x (p₀ / 2) * Real.log x) / (1 + x) := by
  have hexp : (1 - p₀ / 2) + (p₀ - 1) = p₀ / 2 := by ring
  have hmul :
      Real.rpow x (1 - p₀ / 2) * Real.rpow x (p₀ - 1) =
        Real.rpow x (p₀ / 2) := by
    calc
      Real.rpow x (1 - p₀ / 2) * Real.rpow x (p₀ - 1) =
          Real.rpow x ((1 - p₀ / 2) + (p₀ - 1)) :=
        (Real.rpow_add hx0 _ _).symm
      _ = Real.rpow x (p₀ / 2) := by rw [hexp]
  calc
    Real.rpow x (1 - p₀ / 2) *
          (Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x)) =
        (Real.rpow x (1 - p₀ / 2) * Real.rpow x (p₀ - 1)) *
          |Real.log x| / (1 + x) := by ring
    _ = _ := by
      rw [hmul, abs_of_neg (Real.log_neg hx0 hx1)]
      ring

theorem gap6 (p p₀ p₁ L : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    Tendsto
        (fun x =>
          Real.rpow x (1 - p₀ / 2) *
            (Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto
        (fun x => -Real.rpow x (p₀ / 2) * Real.log x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  let l : Filter ℝ := nhdsWithin 0 (Ioi 0)
  let F : ℝ → ℝ := fun x =>
    Real.rpow x (1 - p₀ / 2) *
      (Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x))
  let G : ℝ → ℝ := fun x => -Real.rpow x (p₀ / 2) * Real.log x
  have hlt : ∀ᶠ x : ℝ in l, x < 1 := by
    exact (show ∀ᶠ x : ℝ in nhds (0 : ℝ), x < 1 from
      Iio_mem_nhds (by norm_num)).filter_mono inf_le_left
  have hpos : ∀ᶠ x : ℝ in l, 0 < x := self_mem_nhdsWithin
  have hFG : F =ᶠ[l] fun x => G x / (1 + x) := by
    filter_upwards [hpos, hlt] with x hx0 hx1
    exact zero_weight_eq p₀ x hx0 hx1
  have hGF : G =ᶠ[l] fun x => F x * (1 + x) := by
    filter_upwards [hpos, hlt] with x hx0 hx1
    have hden : 1 + x ≠ 0 := by linarith
    have h := zero_weight_eq p₀ x hx0 hx1
    dsimp [F, G] at h ⊢
    rw [h]
    field_simp
  have hinv :
      Tendsto (fun x : ℝ => (1 + x)⁻¹) l (nhds 1) := by
    have haddAt :
        ContinuousAt (fun x : ℝ => (1 : ℝ) + x) 0 :=
      continuousAt_const.add continuousAt_id
    have hinvAt :
        ContinuousAt (fun x : ℝ => ((1 : ℝ) + x)⁻¹) 0 :=
      haddAt.inv₀ (by norm_num)
    simpa using hinvAt.tendsto.mono_left inf_le_left
  have hadd :
      Tendsto (fun x : ℝ => 1 + x) l (nhds 1) := by
    have haddAt :
        ContinuousAt (fun x : ℝ => (1 : ℝ) + x) 0 :=
      continuousAt_const.add continuousAt_id
    simpa using haddAt.tendsto.mono_left inf_le_left
  change Tendsto F l (nhds L) ↔ Tendsto G l (nhds L)
  constructor
  · intro hF
    have hprod := hF.mul hadd
    have hlim : Tendsto (fun x => F x * (1 + x)) l (nhds L) := by
      convert hprod using 1 <;> simp
    exact hlim.congr' hGF.symm
  · intro hG
    have hprod := hG.mul hinv
    have hlim : Tendsto (fun x => G x / (1 + x)) l (nhds L) := by
      convert hprod using 1 <;> simp [div_eq_mul_inv]
    exact hlim.congr' hFG.symm

theorem gap7 (p p₀ p₁ : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    Tendsto
      (fun x => -Real.rpow x (p₀ / 2) * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hhalf : 0 < p₀ / 2 := by linarith
  have h := (tendsto_log_mul_rpow_nhdsGT_zero hhalf).neg
  convert h using 1
  · funext x
    rw [mul_comm]
    simp
  · simp

theorem gap8 (p p₀ p₁ : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    Tendsto
      (fun x =>
        Real.rpow x (1 - p₀ / 2) *
          (Real.rpow x (p₀ - 1) * |Real.log x| / (1 + x)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact (gap6 p p₀ p₁ 0 hp₀ h₀p hpp₁ hp₁).2
    (gap7 p p₀ p₁ hp₀ h₀p hpp₁ hp₁)

theorem gap9 (p p₀ p₁ x : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) (hx : 1 ≤ x) :
    0 ≤ logKernel p x := by
  unfold logKernel
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
      (Real.log_nonneg hx))
    (by linarith)

theorem gap10 (p p₀ p₁ x : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) (hx : 1 ≤ x) :
    logKernel p x ≤ logKernel p₁ x := by
  have hpow :
      Real.rpow x (p - 1) ≤ Real.rpow x (p₁ - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  unfold logKernel
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (Real.log_nonneg hx))
    (by linarith)

theorem gap11 (p p₀ p₁ x : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) (hx : 1 ≤ x) :
    logKernel p₁ x ≤ Real.rpow x (p₁ - 2) * Real.log x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hdiv :
      Real.rpow x (p₁ - 1) / (1 + x) ≤
        Real.rpow x (p₁ - 1) / x :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) hx0 (by linarith)
  have hpowdiv :
      Real.rpow x (p₁ - 1) / x = Real.rpow x (p₁ - 2) := by
    have hsub :
        Real.rpow x ((p₁ - 1) - 1) =
          Real.rpow x (p₁ - 1) / x := by
      simpa only [Real.rpow_one] using
        Real.rpow_sub hx0 (p₁ - 1) 1
    calc
      Real.rpow x (p₁ - 1) / x =
          Real.rpow x ((p₁ - 1) - 1) := hsub.symm
      _ = Real.rpow x (p₁ - 2) := by
        congr 1
        ring
  calc
    logKernel p₁ x =
        (Real.rpow x (p₁ - 1) / (1 + x)) * Real.log x := by
          unfold logKernel
          ring
    _ ≤ (Real.rpow x (p₁ - 1) / x) * Real.log x :=
      mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg hx)
    _ = Real.rpow x (p₁ - 2) * Real.log x := by rw [hpowdiv]

theorem gap12 (p p₀ p₁ x : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) (hx : 1 ≤ x) :
    0 ≤ Real.rpow x (p₁ - 2) * Real.log x :=
  mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
    (Real.log_nonneg hx)

private theorem rpow_mul_log_integrable_Ioi_one
    (s : ℝ) (hs : s < -1) :
    IntegrableOn (fun x : ℝ => Real.rpow x s * Real.log x)
      (Ioi (1 : ℝ)) volume := by
  let ε : ℝ := (-1 - s) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsexp : s + ε < -1 := by dsimp [ε]; linarith
  have hcont :
      ContinuousOn (fun x : ℝ => Real.rpow x s * Real.log x)
        (Ioi (0 : ℝ)) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 : 0 < x := hx
    exact
      (Real.continuousAt_rpow_const x s (Or.inl hx0.ne')).mul
        (Real.continuousAt_log hx0.ne')
  have hloc :
      LocallyIntegrableOn
        (fun x : ℝ => Real.rpow x s * Real.log x)
        (Ici (1 : ℝ)) volume :=
    (hcont.locallyIntegrableOn measurableSet_Ioi).mono_set (by
      intro x hx
      change 1 ≤ x at hx
      change 0 < x
      exact zero_lt_one.trans_le hx)
  have hOprod :
      (fun x : ℝ => Real.rpow x s * Real.log x) =O[atTop]
        (fun x : ℝ => Real.rpow x s * Real.rpow x ε) :=
    (isBigO_refl (fun x : ℝ => Real.rpow x s) atTop).mul
      (isLittleO_log_rpow_atTop hε).isBigO
  have hO :
      (fun x : ℝ => Real.rpow x s * Real.log x) =O[atTop]
        (fun x : ℝ => Real.rpow x (s + ε)) := by
    refine hOprod.congr' (Eventually.of_forall (fun x => rfl)) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.rpow_add hx s ε).symm
  have hIntIci :
      IntegrableOn (fun x : ℝ => Real.rpow x s * Real.log x)
        (Ici (1 : ℝ)) volume :=
    hloc.integrableOn_of_isBigO_atTop hO
      ((integrableAtFilter_rpow_atTop_iff).2 hsexp)
  exact hIntIci.mono_set (by
    intro x hx
    change 1 < x at hx
    exact hx.le)

theorem gap13 (p p₀ p₁ : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    ∃ L : ℝ,
      HasImproperIntegral 1
        (fun x => Real.rpow x (p₁ - 2) * Real.log x) L := by
  have hs : p₁ - 2 < -1 := by linarith
  have hInt := rpow_mul_log_integrable_Ioi_one (p₁ - 2) hs
  exact ⟨∫ x in Ioi (1 : ℝ),
      Real.rpow x (p₁ - 2) * Real.log x ∂volume,
    intervalIntegral_tendsto_integral_Ioi 1 hInt tendsto_id⟩

theorem gap14 (p p₀ p₁ L : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    Tendsto
        (fun x =>
          Real.rpow x (1 + (1 / 2 : ℝ) * (1 - p₁)) *
            Real.rpow x (p₁ - 2) * Real.log x)
        atTop (nhds L) ↔
      Tendsto
        (fun x =>
          Real.rpow x (-(1 / 2 : ℝ) * (1 - p₁)) * Real.log x)
        atTop (nhds L) := by
  have heq :
      (fun x : ℝ =>
          Real.rpow x (1 + (1 / 2 : ℝ) * (1 - p₁)) *
            Real.rpow x (p₁ - 2) * Real.log x) =ᶠ[atTop]
        (fun x =>
          Real.rpow x (-(1 / 2 : ℝ) * (1 - p₁)) * Real.log x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hmul :
        Real.rpow x (1 + (1 / 2 : ℝ) * (1 - p₁)) *
            Real.rpow x (p₁ - 2) =
          Real.rpow x (-(1 / 2 : ℝ) * (1 - p₁)) := by
      calc
        Real.rpow x (1 + (1 / 2 : ℝ) * (1 - p₁)) *
              Real.rpow x (p₁ - 2) =
            Real.rpow x
              ((1 + (1 / 2 : ℝ) * (1 - p₁)) + (p₁ - 2)) :=
          (Real.rpow_add hx _ _).symm
        _ = Real.rpow x (-(1 / 2 : ℝ) * (1 - p₁)) := by
          congr 1
          ring
    rw [hmul]
  constructor <;> intro h
  · exact h.congr' heq
  · exact h.congr' heq.symm

theorem gap15 (p p₀ p₁ : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    Tendsto
      (fun x =>
        Real.rpow x (-(1 / 2 : ℝ) * (1 - p₁)) * Real.log x)
      atTop (nhds 0) := by
  let ε : ℝ := (1 / 2 : ℝ) * (1 - p₁)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlim :=
    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  have heq :
      (fun x : ℝ => Real.rpow x (-ε) * Real.log x) =ᶠ[atTop]
        (fun x => Real.log x / Real.rpow x ε) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hneg :
        Real.rpow x (-ε) = (Real.rpow x ε)⁻¹ :=
      Real.rpow_neg hx.le ε
    rw [hneg]
    simp only [div_eq_mul_inv]
    rw [mul_comm]
  have hexp : -(1 / 2 : ℝ) * (1 - p₁) = -ε := by
    dsimp [ε]
    ring
  rw [hexp]
  exact hlim.congr' heq.symm

theorem gap16 (p p₀ p₁ : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    Tendsto
      (fun x =>
        Real.rpow x (1 + (1 / 2 : ℝ) * (1 - p₁)) *
          Real.rpow x (p₁ - 2) * Real.log x)
      atTop (nhds 0) := by
  exact (gap14 p p₀ p₁ 0 hp₀ h₀p hpp₁ hp₁).2
    (gap15 p p₀ p₁ hp₀ h₀p hpp₁ hp₁)

private theorem beta_deriv_eq_log_improper
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (fun q => betaFn q (1 - q)) p =
      improperIntegral 0 (logKernel p) := by
  have heq :
      (fun q : ℝ => betaFn q (1 - q)) =ᶠ[nhds p]
        (fun q : ℝ => Real.pi / Real.sin (q * Real.pi)) := by
    filter_upwards [Ioo_mem_nhds hp hp1] with q hq
    exact betaFn_closed q hq.1 hq.2
  calc
    deriv (fun q => betaFn q (1 - q)) p =
        deriv (fun q : ℝ => Real.pi / Real.sin (q * Real.pi)) p :=
      heq.deriv_eq
    _ = -(Real.pi ^ 2 * Real.cos (p * Real.pi) /
          Real.sin (p * Real.pi) ^ 2) := by
      convert (closed_hasDerivAt p hp hp1).deriv using 1 <;> ring
    _ = (∫ x in Ioi (0 : ℝ), logKernel p x ∂volume) := by
      symm
      convert logIntegral_formula p hp hp1 using 1 <;> ring
    _ = improperIntegral 0 (logKernel p) :=
      (improperIntegral_eq_setIntegral
        (logKernel_integrable_of p hp hp1)).symm

theorem gap17 (p p₀ p₁ : ℝ)
    (hp₀ : 0 < p₀) (h₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    (hp₁ : p₁ < 1) :
    deriv (fun q => betaFn q (1 - q)) p =
      improperIntegral 0 (logKernel p) := by
  exact beta_deriv_eq_log_improper p
    (hp₀.trans_le h₀p) (hpp₁.trans_lt hp₁)

theorem gap18 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (fun q => betaFn q (1 - q)) p =
      improperIntegral 0 (logKernel p) := by
  exact beta_deriv_eq_log_improper p hp hp1

theorem gap19 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (fun q => betaFn q (1 - q)) p =
      deriv (fun q => Real.pi / Real.sin (q * Real.pi)) p := by
  have heq :
      (fun q : ℝ => betaFn q (1 - q)) =ᶠ[nhds p]
        (fun q : ℝ => Real.pi / Real.sin (q * Real.pi)) := by
    filter_upwards [Ioo_mem_nhds hp hp1] with q hq
    exact betaFn_closed q hq.1 hq.2
  exact heq.deriv_eq

theorem gap20 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (fun q => Real.pi / Real.sin (q * Real.pi)) p =
      -(Real.pi ^ 2 * Real.cos (p * Real.pi) /
        Real.sin (p * Real.pi) ^ 2) := by
  convert (closed_hasDerivAt p hp hp1).deriv using 1 <;> ring

theorem gap21 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    deriv (fun q => betaFn q (1 - q)) p =
      -(Real.pi ^ 2 * Real.cos (p * Real.pi) /
        Real.sin (p * Real.pi) ^ 2) := by
  rw [gap19 p hp hp1, gap20 p hp hp1]

theorem gap22 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    improperIntegral 0 (logKernel p) =
      -(Real.pi ^ 2 * Real.cos (p * Real.pi) /
        Real.sin (p * Real.pi) ^ 2) := by
  rw [improperIntegral_eq_setIntegral
    (logKernel_integrable_of p hp hp1)]
  convert logIntegral_formula p hp hp1 using 1 <;> ring

end

end ProofGap.Exercise3863
