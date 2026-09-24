import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2381
noncomputable section

open Filter MeasureTheory
open scoped Interval

def weight (p q x : ℝ) : ℝ :=
  Real.rpow x p / (1 + Real.rpow x q)
def integrand (p q x : ℝ) : ℝ := weight p q x * Real.sin x
def absoluteIntegrand (p q x : ℝ) : ℝ := |integrand p q x|
def zeroNormalized (p q x : ℝ) : ℝ :=
  Real.rpow x (-1 - p) * integrand p q x
def zeroModel (q x : ℝ) : ℝ :=
  (Real.sin x / x) * (1 / (1 + Real.rpow x q))

def NearZeroIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioc (0 : ℝ) 1)
def TailConvergent (p q : ℝ) : Prop :=
  ∃ L : ℝ,
    Tendsto (fun A => ∫ x in (1 : ℝ)..A, integrand p q x) atTop (nhds L)
def FullConvergent (p q : ℝ) : Prop :=
  NearZeroIntegrable p q ∧ TailConvergent p q
def TailAbsolutelyIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (absoluteIntegrand p q) (Set.Ioi (1 : ℝ))
def FullAbsolutelyIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (absoluteIntegrand p q) (Set.Ioi (0 : ℝ))

def alpha (p q : ℝ) : ℝ := (q - p - 1) / 2
def absoluteWeighted (p q α x : ℝ) : ℝ :=
  Real.rpow x (q - p - α) * absoluteIntegrand p q x
def absoluteModel (q α x : ℝ) : ℝ :=
  (Real.rpow x q / (1 + Real.rpow x q)) *
    (|Real.sin x| / Real.rpow x α)
def tailFactor (p q x : ℝ) : ℝ :=
  Real.rpow x (p + 1) / (1 + Real.rpow x q)

theorem gap1 (p q : ℝ) (hq : 0 < q) :
    Tendsto (zeroNormalized p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ↔
      Tendsto (zeroModel q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have heq : zeroNormalized p q =ᶠ[nhdsWithin 0 (Set.Ioi 0)] zeroModel q := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hpow : Real.rpow x (-1 - p) * Real.rpow x p = x⁻¹ := by
      calc
        Real.rpow x (-1 - p) * Real.rpow x p =
            Real.rpow x ((-1 - p) + p) := (Real.rpow_add hx (-1 - p) p).symm
        _ = Real.rpow x (-1) := by congr 1 <;> ring
        _ = (Real.rpow x 1)⁻¹ := Real.rpow_neg hx.le 1
        _ = x⁻¹ := by
          have hone : Real.rpow x 1 = x := by simpa using Real.rpow_one x
          rw [hone]
    simp only [zeroNormalized, integrand, weight, zeroModel]
    calc
      Real.rpow x (-1 - p) *
          (Real.rpow x p / (1 + Real.rpow x q) * Real.sin x) =
          (Real.rpow x (-1 - p) * Real.rpow x p) *
            (Real.sin x / (1 + Real.rpow x q)) := by ring
      _ = (Real.sin x / x) * (1 / (1 + Real.rpow x q)) := by
        rw [hpow]
        simp only [div_eq_mul_inv, one_div]
        ring
  exact ⟨fun h => h.congr' heq, fun h => h.congr' heq.symm⟩

theorem gap2 (q : ℝ) (hq : 0 < q) :
    Tendsto (zeroModel q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hsinc : Tendsto (fun x : ℝ => Real.sin x / x) l (nhds 1) := by
    have hbase : Tendsto Real.sinc l (nhds 1) := by
      have hmono := (Real.continuous_sinc.tendsto 0).mono_left
        (show l ≤ nhds 0 by
          dsimp only [l, nhdsWithin]
          exact inf_le_left)
      simpa using hmono
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sinc_of_ne_zero hx.ne'
  have hrpow : Tendsto (fun x : ℝ => Real.rpow x q) l (nhds 0) := by
    have hmono := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).mono_left
      (show l ≤ nhds 0 by
        dsimp only [l, nhdsWithin]
        exact inf_le_left)
    simpa [Real.zero_rpow hq.ne'] using hmono
  have hden : Tendsto (fun x : ℝ => 1 / (1 + Real.rpow x q)) l (nhds 1) := by
    have h := (tendsto_const_nhds.add hrpow).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa [one_div] using h
  simpa only [zeroModel, one_mul] using hsinc.mul hden

theorem gap3 (p q : ℝ) (hq : 0 < q) :
    Tendsto (zeroNormalized p q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  exact (gap1 p q hq).mpr (gap2 q hq)

private theorem measurable_rpow (r : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x r) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  exact (Real.continuousAt_rpow_const x r
    (Or.inl (by simpa using hx))).continuousWithinAt

private theorem measurable_integrand (p q : ℝ) : Measurable (integrand p q) := by
  unfold integrand weight
  exact ((measurable_rpow p).div (measurable_const.add (measurable_rpow q))).mul
    Real.measurable_sin

private theorem continuousOn_integrand_Ioi (p q : ℝ) :
    ContinuousOn (integrand p q) (Set.Ioi 0) := by
  intro x hx
  have hp : ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hx.ne')
  have hq : ContinuousAt (fun y : ℝ => Real.rpow y q) x :=
    Real.continuousAt_rpow_const x q (Or.inl hx.ne')
  have hden : 1 + Real.rpow x q ≠ 0 := by
    have hpow : 0 < Real.rpow x q := by
      simpa using Real.rpow_pos_of_pos hx q
    exact ne_of_gt (by linarith)
  exact ((hp.div (continuousAt_const.add hq) hden).mul Real.continuous_sin.continuousAt).continuousWithinAt

private theorem continuousOn_rpow_Ioi (r : ℝ) :
    ContinuousOn (fun x : ℝ => Real.rpow x r) (Set.Ioi 0) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x r (Or.inl hx.ne')).continuousWithinAt

private theorem integrableOn_Ioc_iff_integrableAtFilter_nhdsGT
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi 0)) :
    IntegrableOn f (Set.Ioc (0 : ℝ) 1) ↔
      IntegrableAtFilter f (nhdsWithin 0 (Set.Ioi 0)) := by
  constructor
  · intro hint
    refine ⟨Set.Ioc (0 : ℝ) 1, ?_, hint⟩
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Iio 1, Iio_mem_nhds zero_lt_one, fun x hx => ⟨hx.2, hx.1.le⟩⟩
  · rintro ⟨s, hs, hint⟩
    obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs
    obtain ⟨l, r, hzero, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
    let δ := min (r / 2) (1 / 2)
    have hδ : 0 < δ := lt_min (half_pos hzero.2) (by norm_num)
    have hδone : δ ≤ 1 := by
      dsimp only [δ]
      linarith [min_le_right (r / 2) (1 / 2)]
    have hnear : IntegrableOn f (Set.Ioc (0 : ℝ) δ) :=
      hint.mono_set fun x hx => hus ⟨hlu ⟨by linarith [hzero.1, hx.1], by
        dsimp only [δ] at hx
        linarith [min_le_left (r / 2) (1 / 2), hx.2]⟩, hx.1⟩
    have hfar : IntegrableOn f (Set.Icc δ 1) := by
      have hc : ContinuousOn f (Set.Icc δ 1) :=
        hf.mono fun x hx => lt_of_lt_of_le hδ hx.1
      exact hc.integrableOn_compact isCompact_Icc
    refine (hnear.union hfar).mono_set ?_
    intro x hx
    by_cases hxd : x ≤ δ
    · exact Set.mem_union_left _ ⟨hx.1, hxd⟩
    · exact Set.mem_union_right _ ⟨le_of_not_ge hxd, hx.2⟩

private theorem tendsto_zeroNormalized_of_q_zero (p : ℝ) :
    Tendsto (zeroNormalized p 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hsinc : Tendsto (fun x : ℝ => Real.sin x / x) l (nhds 1) := by
    have hbase : Tendsto Real.sinc l (nhds 1) := by
      have hmono := (Real.continuous_sinc.tendsto 0).mono_left
        (show l ≤ nhds 0 by
          dsimp only [l, nhdsWithin]
          exact inf_le_left)
      simpa using hmono
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sinc_of_ne_zero hx.ne'
  have hlim : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * (Real.sin x / x)) l (nhds (1 / 2)) := by
    simpa using (tendsto_const_nhds.mul hsinc)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hpow : Real.rpow x (-1 - p) * Real.rpow x p = x⁻¹ := by
    calc
      Real.rpow x (-1 - p) * Real.rpow x p =
          Real.rpow x ((-1 - p) + p) := (Real.rpow_add hx (-1 - p) p).symm
      _ = Real.rpow x (-1) := by congr 1 <;> ring
      _ = (Real.rpow x 1)⁻¹ := Real.rpow_neg hx.le 1
      _ = x⁻¹ := by
        have hone : Real.rpow x 1 = x := by simpa using Real.rpow_one x
        rw [hone]
  simp only [zeroNormalized, integrand, weight]
  rw [show Real.rpow x 0 = 1 from Real.rpow_zero x]
  rw [show Real.rpow x (-1 - p) * (Real.rpow x p / (1 + 1) * Real.sin x) =
      (Real.rpow x (-1 - p) * Real.rpow x p) * (Real.sin x / 2) by ring, hpow]
  simp only [div_eq_mul_inv]
  ring

theorem gap4 (p q : ℝ) (hq : 0 ≤ q) :
    NearZeroIntegrable p q ↔ -2 < p := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let g : ℝ → ℝ := fun x => Real.rpow x (p + 1)
  haveI : IsMeasurablyGenerated l := by
    dsimp only [l]
    exact measurableSet_Ioi.nhdsWithin_isMeasurablyGenerated _
  have hnorm : ∃ c : ℝ, c ≠ 0 ∧ Tendsto (zeroNormalized p q) l (nhds c) := by
    rcases hq.eq_or_lt with rfl | hq
    · exact ⟨1 / 2, by norm_num, tendsto_zeroNormalized_of_q_zero p⟩
    · exact ⟨1, one_ne_zero, gap3 p q hq⟩
  obtain ⟨c, hc, hnorm⟩ := hnorm
  have hratio : Tendsto (fun x => integrand p q x / g x) l (nhds c) := by
    refine hnorm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hneg : Real.rpow x (-1 - p) = (Real.rpow x (p + 1))⁻¹ := by
      calc
        Real.rpow x (-1 - p) = Real.rpow x (-(p + 1)) := by congr 1 <;> ring
        _ = (Real.rpow x (p + 1))⁻¹ := Real.rpow_neg hx.le (p + 1)
    simp only [zeroNormalized, g]
    rw [hneg]
    simp only [div_eq_mul_inv]
    ac_rfl
  have htheta : g =Θ[l] integrand p q :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero hratio hc
  have hmeasG : StronglyMeasurableAtFilter g l :=
    (measurable_rpow (p + 1)).stronglyMeasurable.stronglyMeasurableAtFilter
  have hmeasF : StronglyMeasurableAtFilter (integrand p q) l :=
    (measurable_integrand p q).stronglyMeasurable.stronglyMeasurableAtFilter
  have hfilter : IntegrableAtFilter (integrand p q) l ↔ IntegrableAtFilter g l :=
    ⟨fun hf => htheta.1.integrableAtFilter hmeasG hf,
      fun hg => htheta.2.integrableAtFilter hmeasF hg⟩
  have hIocG : IntegrableOn g (Set.Ioc (0 : ℝ) 1) ↔ -2 < p := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (p + 1)) (Set.Ioo 0 1) ↔
        -1 < p + 1 := by
      simpa using (intervalIntegral.integrableOn_Ioo_rpow_iff (s := p + 1) zero_lt_one)
    rw [hpow]
    constructor <;> intro h <;> linarith
  unfold NearZeroIntegrable
  rw [integrableOn_Ioc_iff_integrableAtFilter_nhdsGT
    (integrand p q) (continuousOn_integrand_Ioi p q)]
  rw [hfilter]
  rw [← integrableOn_Ioc_iff_integrableAtFilter_nhdsGT g (continuousOn_rpow_Ioi (p + 1))]
  exact hIocG

theorem gap5 (p q A : ℝ) (hq : 0 ≤ q) (hpq : q ≤ p) (hA : 1 < A) :
    ∃ N : ℕ, 0 < N ∧ A < 2 * (N : ℝ) * Real.pi + Real.pi / 4 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((A - Real.pi / 4) / (2 * Real.pi)))
  refine ⟨N, ?_, ?_⟩
  · have hNnat : 1 < N := by
      exact_mod_cast (lt_of_le_of_lt (le_max_left 1 _) hN)
    omega
  · have hratio : (A - Real.pi / 4) / (2 * Real.pi) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right 1 _) hN
    have hden : 0 < (2 : ℝ) * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hm := (div_lt_iff₀ hden).mp hratio
    nlinarith

theorem gap6 (p q : ℝ) (hq : 0 ≤ q) (hpq : q ≤ p) :
    ∀ B : ℝ, ∃ A' A'' : ℝ, B ≤ A' ∧ A' ≤ A'' ∧
      |∫ x in A'..A'', integrand p q x| > Real.sqrt 2 / 6 := by
  intro B
  obtain ⟨N, hN, hBN⟩ := gap5 p q (max B 2) hq hpq
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right B 2))
  let A' : ℝ := 2 * (N : ℝ) * Real.pi + Real.pi / 4
  let A'' : ℝ := 2 * (N : ℝ) * Real.pi + 3 * Real.pi / 4
  change max B 2 < A' at hBN
  have hAA : A' ≤ A'' := by
    dsimp only [A', A'']
    nlinarith [Real.pi_pos]
  have hAone : 1 < A' := by
    exact (by norm_num : (1 : ℝ) < 2) |>.trans ((le_max_right B 2).trans_lt hBN)
  have hcosA' : Real.cos A' = Real.sqrt 2 / 2 := by
    rw [show A' = Real.pi / 4 + (N : ℝ) * (2 * Real.pi) by
      dsimp only [A']; ring]
    simpa using Real.cos_add_nat_mul_two_pi (Real.pi / 4) N
  have hcosA'' : Real.cos A'' = -(Real.sqrt 2 / 2) := by
    rw [show A'' = (Real.pi - Real.pi / 4) + (N : ℝ) * (2 * Real.pi) by
      dsimp only [A'']; ring]
    rw [Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub, Real.cos_pi_div_four]
  have hlowerInt : IntervalIntegrable (fun x : ℝ => (1 / 2 : ℝ) * Real.sin x)
      volume A' A'' := Real.continuous_sin.const_mul (1 / 2 : ℝ) |>.intervalIntegrable _ _
  have hintegrandInt : IntervalIntegrable (integrand p q) volume A' A'' := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_integrand_Ioi p q).mono fun x hx => by
      rw [Set.uIcc_of_le hAA] at hx
      exact zero_lt_one.trans (hAone.trans_le hx.1)
  have hpoint : ∀ x ∈ Set.Icc A' A'',
      (1 / 2 : ℝ) * Real.sin x ≤ integrand p q x := by
    intro x hx
    have hxone : 1 ≤ x := hAone.le.trans hx.1
    have hxpos : 0 < x := zero_lt_one.trans_le hxone
    let y : ℝ := x - (N : ℝ) * (2 * Real.pi)
    have hy0 : 0 ≤ y := by
      have hbase : (N : ℝ) * (2 * Real.pi) + Real.pi / 4 ≤ x := by
        convert hx.1 using 1 <;> ring
      dsimp only [y]
      nlinarith [Real.pi_pos]
    have hypi : y ≤ Real.pi := by
      have htop : x ≤ (N : ℝ) * (2 * Real.pi) + 3 * Real.pi / 4 := by
        convert hx.2 using 1 <;> ring
      dsimp only [y]
      nlinarith [Real.pi_pos]
    have hsin : 0 ≤ Real.sin x := by
      have hy := Real.sin_nonneg_of_nonneg_of_le_pi hy0 hypi
      have hper := Real.sin_sub_nat_mul_two_pi x N
      simpa only [y] using hper ▸ hy
    have hxq : 1 ≤ Real.rpow x q := by
      simpa using Real.one_le_rpow hxone hq
    have hpqpow : Real.rpow x q ≤ Real.rpow x p :=
      Real.rpow_le_rpow_of_exponent_le hxone hpq
    have hweight : (1 / 2 : ℝ) ≤ weight p q x := by
      unfold weight
      rw [le_div_iff₀ (by positivity : 0 < 1 + Real.rpow x q)]
      nlinarith
    unfold integrand
    exact mul_le_mul_of_nonneg_right hweight hsin
  have hmono : (∫ x in A'..A'', (1 / 2 : ℝ) * Real.sin x) ≤
      ∫ x in A'..A'', integrand p q x :=
    intervalIntegral.integral_mono_on hAA hlowerInt hintegrandInt hpoint
  rw [intervalIntegral.integral_const_mul, integral_sin, hcosA', hcosA''] at hmono
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨A', A'', ?_, hAA, ?_⟩
  · exact (le_max_left B 2).trans hBN.le
  · have hpos : 0 < ∫ x in A'..A'', integrand p q x := by
      nlinarith
    rw [abs_of_pos hpos]
    nlinarith

theorem gap7 (p q : ℝ) (hq : 0 ≤ q) (hpq : q ≤ p) :
    ¬ TailConvergent p q := by
  rintro ⟨L, hL⟩
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hclose : ∀ᶠ A : ℝ in atTop,
      dist (∫ x in (1 : ℝ)..A, integrand p q x) L < Real.sqrt 2 / 12 :=
    (Metric.tendsto_nhds.1 hL) _ (by positivity)
  obtain ⟨B, hB⟩ := eventually_atTop.1 hclose
  obtain ⟨A', A'', hBA', hAA, hlarge⟩ := gap6 p q hq hpq (max B 1)
  have hA'B : B ≤ A' := (le_max_left B 1).trans hBA'
  have hA''B : B ≤ A'' := hA'B.trans hAA
  have hA'one : 1 ≤ A' := (le_max_right B 1).trans hBA'
  have hA''one : 1 ≤ A'' := hA'one.trans hAA
  have hfirst : IntervalIntegrable (integrand p q) volume (1 : ℝ) A' := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_integrand_Ioi p q).mono fun x hx => by
      rw [Set.uIcc_of_le hA'one] at hx
      exact zero_lt_one.trans_le hx.1
  have hsecond : IntervalIntegrable (integrand p q) volume A' A'' := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_integrand_Ioi p q).mono fun x hx => by
      rw [Set.uIcc_of_le hAA] at hx
      exact zero_lt_one.trans_le (hA'one.trans hx.1)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hfirst hsecond
  have hdist' := hB A' hA'B
  have hdist'' := hB A'' hA''B
  rw [Real.dist_eq] at hdist' hdist''
  have hIeq : (∫ x in A'..A'', integrand p q x) =
      (∫ x in (1 : ℝ)..A'', integrand p q x) -
        ∫ x in (1 : ℝ)..A', integrand p q x := by
    linarith [hadd]
  have hsmall : |∫ x in A'..A'', integrand p q x| < Real.sqrt 2 / 6 := by
    rw [hIeq]
    calc
      |(∫ x in (1 : ℝ)..A'', integrand p q x) -
          ∫ x in (1 : ℝ)..A', integrand p q x| ≤
          |(∫ x in (1 : ℝ)..A'', integrand p q x) - L| +
            |(∫ x in (1 : ℝ)..A', integrand p q x) - L| := by
        rw [show (∫ x in (1 : ℝ)..A'', integrand p q x) -
            ∫ x in (1 : ℝ)..A', integrand p q x =
          ((∫ x in (1 : ℝ)..A'', integrand p q x) - L) -
            ((∫ x in (1 : ℝ)..A', integrand p q x) - L) by ring]
        exact abs_sub _ _
      _ < Real.sqrt 2 / 6 := by linarith
  linarith

theorem gap8 (p q : ℝ) (hpq : p < q - 1) :
    0 < alpha p q := by
  dsimp only [alpha]
  linarith

theorem gap9 (p q : ℝ) (hpq : p < q - 1) :
    p + alpha p q < q - 1 := by
  dsimp only [alpha]
  linarith

theorem gap10 (p q : ℝ) (hq : 0 < q) (hpq : p < q - 1) :
    Tendsto (absoluteWeighted p q (alpha p q)) atTop (nhds 0) ↔
      Tendsto (absoluteModel q (alpha p q)) atTop (nhds 0) := by
  have heq : absoluteWeighted p q (alpha p q) =ᶠ[atTop]
      absoluteModel q (alpha p q) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hqpos : 0 < Real.rpow x q := by
      simpa using Real.rpow_pos_of_pos hx q
    have hpPos : 0 < Real.rpow x p := by
      simpa using Real.rpow_pos_of_pos hx p
    have hden : 0 < 1 + Real.rpow x q := by linarith
    have hw : 0 < weight p q x := by
      exact div_pos hpPos hden
    have hmul : Real.rpow x (q - p - alpha p q) * Real.rpow x p =
        Real.rpow x (q - alpha p q) := by
      calc
        _ = Real.rpow x ((q - p - alpha p q) + p) :=
          (Real.rpow_add hx (q - p - alpha p q) p).symm
        _ = _ := by congr 1 <;> ring
    have hsub : Real.rpow x (q - alpha p q) =
        Real.rpow x q / Real.rpow x (alpha p q) := by
      simpa using Real.rpow_sub hx q (alpha p q)
    simp only [absoluteWeighted, absoluteIntegrand, integrand, abs_mul]
    rw [abs_of_pos hw]
    simp only [absoluteModel, weight]
    rw [show Real.rpow x (q - p - alpha p q) *
        (Real.rpow x p / (1 + Real.rpow x q) * |Real.sin x|) =
        (Real.rpow x (q - p - alpha p q) * Real.rpow x p) /
          (1 + Real.rpow x q) * |Real.sin x| by ring]
    rw [hmul, hsub]
    ring
  exact ⟨fun h => h.congr' heq, fun h => h.congr' heq.symm⟩

theorem gap11 (p q : ℝ) (hq : 0 < q) (hpq : p < q - 1) :
    Tendsto (absoluteModel q (alpha p q)) atTop (nhds 0) := by
  have hqTop : Tendsto (fun x : ℝ => Real.rpow x q) atTop atTop := by
    simpa using tendsto_rpow_atTop hq
  have hdenTop : Tendsto (fun x : ℝ => 1 + Real.rpow x q) atTop atTop :=
    (show Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).add_atTop hqTop
  have hrecip : Tendsto (fun x : ℝ => 1 / (1 + Real.rpow x q)) atTop (nhds 0) :=
    hdenTop.const_div_atTop 1
  have hfactor : Tendsto (fun x : ℝ => Real.rpow x q / (1 + Real.rpow x q))
      atTop (nhds 1) := by
    have hlim : Tendsto (fun x : ℝ => 1 - 1 / (1 + Real.rpow x q)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hrecip
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hpow : 0 < Real.rpow x q := by
      simpa using Real.rpow_pos_of_pos hx q
    field_simp [ne_of_gt (by linarith : 0 < 1 + Real.rpow x q)]
    ring
  have halpha : 0 < alpha p q := gap8 p q hpq
  have hpowTop : Tendsto (fun x : ℝ => Real.rpow x (alpha p q)) atTop atTop := by
    simpa using tendsto_rpow_atTop halpha
  have hsin : Tendsto
      (fun x : ℝ => |Real.sin x| / Real.rpow x (alpha p q)) atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Filter.Eventually.of_forall fun x => abs_nonneg (Real.sin x))
      (Filter.Eventually.of_forall Real.abs_sin_le_one) hpowTop
  simpa only [absoluteModel, mul_zero] using hfactor.mul hsin

theorem gap12 (p q : ℝ) (hq : 0 < q) (hpq : p < q - 1) :
    Tendsto (absoluteWeighted p q (alpha p q)) atTop (nhds 0) := by
  exact (gap10 p q hq hpq).mpr (gap11 p q hq hpq)

theorem gap13 (p q : ℝ) (hq : 0 ≤ q) (hpq : p < q - 1) :
    TailAbsolutelyIntegrable p q := by
  rcases hq.eq_or_lt with hqzero | hqpos
  · subst q
    have href : IntegrableOn (fun x : ℝ => Real.rpow x p) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    unfold TailAbsolutelyIntegrable
    have hmeas : AEStronglyMeasurable (absoluteIntegrand p 0)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      ((continuousOn_integrand_Ioi p 0).abs.mono fun x hx =>
        (show 0 < x from lt_trans zero_lt_one hx)).aestronglyMeasurable measurableSet_Ioi
    apply href.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxp : 0 < Real.rpow x p := by
      simpa using Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) p
    have hsin := Real.abs_sin_le_one x
    have hz : Real.rpow x 0 = 1 := Real.rpow_zero x
    simp only [Real.norm_eq_abs, absoluteIntegrand, abs_abs, integrand, weight]
    rw [hz]
    rw [abs_mul, abs_of_pos (div_pos hxp (by norm_num : (0 : ℝ) < 1 + 1))]
    apply (mul_le_of_le_one_right (by positivity) hsin).trans
    linarith
  let β := q - p - alpha p q
  let g : ℝ → ℝ := fun x => Real.rpow x (-β)
  have hβ : 1 < β := by
    dsimp only [β]
    linarith [gap9 p q hpq]
  have hratio : Tendsto (fun x => absoluteIntegrand p q x / g x) atTop (nhds 0) := by
    refine (gap12 p q hqpos hpq).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hneg : Real.rpow x (-β) = (Real.rpow x β)⁻¹ :=
      Real.rpow_neg hx.le β
    simp only [absoluteWeighted, g]
    rw [hneg]
    simp only [div_eq_mul_inv, inv_inv]
    ac_rfl
  have hO : absoluteIntegrand p q =O[atTop] g :=
    Asymptotics.isBigO_of_div_tendsto_nhds (by
      filter_upwards [eventually_gt_atTop 0] with x hx hzero
      have hpos : 0 < g x := by
        dsimp only [g]
        simpa using Real.rpow_pos_of_pos hx (-β)
      exact (hpos.ne' hzero).elim) 0 hratio
  have hg : IntegrableAtFilter g atTop := by
    have hpow : IntegrableAtFilter (fun x : ℝ => Real.rpow x (-β)) atTop ↔
        -β < -1 := by
      simpa using (integrableAtFilter_rpow_atTop_iff (s := -β))
    exact hpow.mpr (by linarith)
  have hcont : ContinuousOn (absoluteIntegrand p q) (Set.Ici (1 : ℝ)) := by
    exact (continuousOn_integrand_Ioi p q).abs.mono fun x hx =>
      (show 0 < x from lt_of_lt_of_le zero_lt_one hx)
  have hlocal : LocallyIntegrableOn (absoluteIntegrand p q) (Set.Ici (1 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ici
  unfold TailAbsolutelyIntegrable
  exact (hlocal.integrableOn_of_isBigO_atTop hO hg).mono_set Set.Ioi_subset_Ici_self

theorem gap14 (p q : ℝ) (hq : 0 < q)
    (hpLower : q - 1 ≤ p) (hpUpper : p < q) :
    ∃ A₀ > 1, ∀ x ≥ A₀, 1 / 3 < tailFactor p q x := by
  refine ⟨2, by norm_num, ?_⟩
  intro x hx
  have hxone : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hxpos : 0 < x := lt_trans zero_lt_one hxone
  have hr : 0 ≤ p + 1 - q := by linarith
  have hxr : 1 ≤ Real.rpow x (p + 1 - q) := by
    simpa using Real.one_le_rpow hxone.le hr
  have hxq : 1 < Real.rpow x q := by
    simpa using Real.one_lt_rpow hxone hq
  have hadd : Real.rpow x (p + 1) =
      Real.rpow x (p + 1 - q) * Real.rpow x q := by
    calc
      _ = Real.rpow x ((p + 1 - q) + q) := by congr 1 <;> ring
      _ = _ := Real.rpow_add hxpos (p + 1 - q) q
  have hmul : Real.rpow x q ≤
      Real.rpow x (p + 1 - q) * Real.rpow x q :=
    le_mul_of_one_le_left (le_trans zero_le_one hxq.le) hxr
  simp only [tailFactor]
  rw [hadd]
  rw [lt_div_iff₀ (by linarith : 0 < 1 + Real.rpow x q)]
  nlinarith

theorem gap15 (p q : ℝ) (hq : 0 < q)
    (hpLower : q - 1 ≤ p) (hpUpper : p < q) :
    ∃ A₀ > 1, ∀ x ≥ A₀,
      (1 / 3 : ℝ) * |Real.sin x / x| ≤ absoluteIntegrand p q x := by
  obtain ⟨A₀, hA₀, hfactor⟩ := gap14 p q hq hpLower hpUpper
  refine ⟨A₀, hA₀, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_trans zero_lt_one (hA₀.trans_le hx)
  have hpPos : 0 < Real.rpow x p := by
    simpa using Real.rpow_pos_of_pos hxpos p
  have hqPos : 0 < Real.rpow x q := by
    simpa using Real.rpow_pos_of_pos hxpos q
  have hden : 0 < 1 + Real.rpow x q := by linarith
  have hw : 0 < weight p q x := div_pos hpPos hden
  calc
    (1 / 3 : ℝ) * |Real.sin x / x| ≤
        tailFactor p q x * |Real.sin x / x| :=
      mul_le_mul_of_nonneg_right (le_of_lt (hfactor x hx)) (abs_nonneg _)
    _ = absoluteIntegrand p q x := by
      have hpadd : Real.rpow x (p + 1) = Real.rpow x p * x := by
        calc
          _ = Real.rpow x (p + 1) := rfl
          _ = Real.rpow x p * Real.rpow x 1 := Real.rpow_add hxpos p 1
          _ = _ := by
            have hone : Real.rpow x 1 = x := by simpa using Real.rpow_one x
            rw [hone]
      have habsdiv : |Real.sin x / x| = |Real.sin x| / x := by
        rw [abs_div, abs_of_pos hxpos]
      rw [habsdiv]
      simp only [tailFactor, absoluteIntegrand, integrand, abs_mul]
      rw [abs_of_pos hw]
      simp only [weight]
      rw [hpadd]
      field_simp [hxpos.ne', hden.ne']
      <;> ring

private theorem cos_two_mul_div_tail_convergent (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, Tendsto (fun A => ∫ x in a..A, Real.cos (2 * x) / x)
      atTop (nhds C) := by
  let w : ℝ → ℝ := fun x => Real.rpow x (-1 : ℝ)
  let w' : ℝ → ℝ := fun x => -Real.rpow x (-2 : ℝ)
  let v : ℝ → ℝ := fun x => Real.sin (2 * x) / 2
  have hwderiv : ∀ x ∈ Set.Ici a, HasDerivAt w (w' x) x := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx
    have h := Real.hasDerivAt_rpow_const (x := x) (p := (-1 : ℝ)) (Or.inl hxpos.ne')
    simpa only [w, w', show (-1 : ℝ) - 1 = -2 by norm_num, neg_one_mul] using h
  have hvderiv : ∀ x : ℝ, HasDerivAt v (Real.cos (2 * x)) x := by
    intro x
    have harg : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have h := ((Real.hasDerivAt_sin (2 * x)).comp x harg).div_const 2
    simpa only [v] using h.congr_deriv (by ring)
  have hrpow : IntegrableOn (fun x : ℝ => Real.rpow x (-2 : ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  have hw' : IntegrableOn w' (Set.Ioi a) := by
    simpa only [w'] using hrpow.neg
  have hvcont : Continuous v := by
    dsimp only [v]
    fun_prop
  have hvmeas : AEStronglyMeasurable v (volume.restrict (Set.Ioi a)) :=
    hvcont.stronglyMeasurable.aestronglyMeasurable
  have hprod : IntegrableOn (fun x => w' x * v x) (Set.Ioi a) := by
    exact hw'.integrable.mul_bdd hvmeas (Filter.Eventually.of_forall fun x => by
      show ‖v x‖ ≤ (1 : ℝ)
      have hs := Real.abs_sin_le_one (2 * x)
      dsimp only [v]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num at hs ⊢
      linarith)
  have hJ := MeasureTheory.intervalIntegral_tendsto_integral_Ioi
    a hprod tendsto_id
  have hw0 : Tendsto w atTop (nhds 0) := by
    simpa only [w] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)
  have hboundary : Tendsto (fun A => w A * v A) atTop (nhds 0) := by
    have hmul : Tendsto (fun A => v A * w A) atTop (nhds 0) :=
      bdd_le_mul_tendsto_zero (b := (-1 : ℝ)) (B := (1 : ℝ))
        (Filter.Eventually.of_forall fun x => by
          have hs := (abs_le.mp (Real.abs_sin_le_one (2 * x))).1
          dsimp only [v]
          linarith)
        (Filter.Eventually.of_forall fun x => by
          have hs := (abs_le.mp (Real.abs_sin_le_one (2 * x))).2
          dsimp only [v]
          linarith) hw0
    simpa only [mul_comm] using hmul
  let C := -(w a * v a) - ∫ x in Set.Ioi a, w' x * v x
  refine ⟨C, ?_⟩
  have hlim : Tendsto
      (fun A => w A * v A - w a * v a - ∫ x in a..A, w' x * v x)
      atTop (nhds C) := by
    simpa only [C, zero_sub] using
      (hboundary.sub tendsto_const_nhds).sub hJ
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop a] with A hA
  have hwcont : ContinuousOn w (Set.uIcc a A) := by
    rw [Set.uIcc_of_le hA]
    intro x hx
    exact (hwderiv x hx.1).continuousAt.continuousWithinAt
  have hw'int : IntervalIntegrable w' volume a A := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hA]
    exact hw'.mono_set Set.Ioc_subset_Ioi_self
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := a) (b := A) (u := w) (v := v) (u' := w')
    (v' := fun x => Real.cos (2 * x)) hwcont hvcont.continuousOn
    (fun x hx => hwderiv x (by
      rw [min_eq_left hA, max_eq_right hA] at hx
      exact hx.1.le))
    (fun x _ => hvderiv x) hw'int
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
  calc
    w A * v A - w a * v a - ∫ x in a..A, w' x * v x =
        ∫ x in a..A, w x * Real.cos (2 * x) := by simpa only using hparts.symm
    _ = ∫ x in a..A, Real.cos (2 * x) / x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hwx : w x = x⁻¹ := by simpa only [w] using Real.rpow_neg_one x
      change w x * Real.cos (2 * x) = Real.cos (2 * x) / x
      rw [hwx]
      simp only [div_eq_mul_inv, mul_comm]

private theorem sin_sq_div_integral_tendsto_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun A => ∫ x in a..A, Real.sin x ^ 2 / x) atTop atTop := by
  obtain ⟨C, hcos⟩ := cos_two_mul_div_tail_convergent a ha
  have hdiv : Tendsto (fun A : ℝ => A / a) atTop atTop :=
    tendsto_id.atTop_div_const ha
  have hlog : Tendsto (fun A : ℝ => Real.log (A / a)) atTop atTop :=
    Real.tendsto_log_atTop.comp hdiv
  have hmain : Tendsto (fun A : ℝ => (1 / 2 : ℝ) * Real.log (A / a))
      atTop atTop := by
    have h := hlog.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [mul_comm] using h
  have hcosScaled : Tendsto
      (fun A => (1 / 2 : ℝ) * ∫ x in a..A, Real.cos (2 * x) / x)
      atTop (nhds ((1 / 2 : ℝ) * C)) := tendsto_const_nhds.mul hcos
  have hcombined : Tendsto
      (fun A => (1 / 2 : ℝ) * Real.log (A / a) -
        (1 / 2 : ℝ) * ∫ x in a..A, Real.cos (2 * x) / x) atTop atTop := by
    have h := hcosScaled.neg.add_atTop hmain
    simpa only [sub_eq_add_neg, add_comm] using h
  refine hcombined.congr' ?_
  filter_upwards [eventually_gt_atTop a] with A hA
  have hApos : 0 < A := ha.trans hA
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a A := by
    exact (continuousOn_inv₀.mono fun x hx => by
      rw [Set.uIcc_of_le hA.le] at hx
      exact (ha.trans_le hx.1).ne').intervalIntegrable
  have hcosInt : IntervalIntegrable (fun x : ℝ => Real.cos (2 * x) / x)
      volume a A := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hA.le]
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    have hnum : ContinuousAt (fun y : ℝ => Real.cos (2 * y)) x := by fun_prop
    exact (hnum.div continuousAt_id hxpos.ne').continuousWithinAt
  calc
    (1 / 2 : ℝ) * Real.log (A / a) -
        (1 / 2 : ℝ) * ∫ x in a..A, Real.cos (2 * x) / x =
        ∫ x in a..A, (1 / 2 : ℝ) * x⁻¹ -
          (1 / 2 : ℝ) * (Real.cos (2 * x) / x) := by
      rw [intervalIntegral.integral_sub (hinv.const_mul (1 / 2))
        (hcosInt.const_mul (1 / 2)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_inv_of_pos ha hApos]
    _ = ∫ x in a..A, Real.sin x ^ 2 / x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hA.le] at hx
      have hxpos : 0 < x := ha.trans_le hx.1
      have htrig : Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
        rw [Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq x]
      change (1 / 2 : ℝ) * x⁻¹ - (1 / 2 : ℝ) * (Real.cos (2 * x) / x) =
        Real.sin x ^ 2 / x
      rw [htrig]
      field_simp [hxpos.ne']

theorem gap16 (A₀ : ℝ) (hA₀ : 1 < A₀) :
    Tendsto (fun A => (1 / 3 : ℝ) *
      ∫ x in A₀..A, |Real.sin x / x|) atTop atTop := by
  have hlower := sin_sq_div_integral_tendsto_atTop A₀ (zero_lt_one.trans hA₀)
  have hscaled : Tendsto
      (fun A => (1 / 3 : ℝ) * ∫ x in A₀..A, Real.sin x ^ 2 / x)
      atTop atTop := by
    have h := hlower.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 3)
    simpa only [mul_comm] using h
  have hle : ∀ᶠ A : ℝ in atTop,
      (1 / 3 : ℝ) * (∫ x in A₀..A, Real.sin x ^ 2 / x) ≤
        (1 / 3 : ℝ) * ∫ x in A₀..A, |Real.sin x / x| := by
    filter_upwards [eventually_ge_atTop A₀] with A hA
    have hlowerInt : IntervalIntegrable (fun x : ℝ =>
        (1 / 3 : ℝ) * (Real.sin x ^ 2 / x)) volume A₀ A := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hA]
      intro x hx
      fun_prop (disch := have := (zero_lt_one.trans hA₀).trans_le hx.1; positivity)
    have habsInt : IntervalIntegrable (fun x : ℝ =>
        (1 / 3 : ℝ) * |Real.sin x / x|) volume A₀ A := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hA]
      intro x hx
      fun_prop (disch := have := (zero_lt_one.trans hA₀).trans_le hx.1; positivity)
    have hmono := intervalIntegral.integral_mono_on hA hlowerInt habsInt (fun x hx => by
      have hxpos : 0 < x := (zero_lt_one.trans hA₀).trans_le hx.1
      have hs0 : 0 ≤ |Real.sin x| := abs_nonneg _
      have hs1 : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
      have hsq : Real.sin x ^ 2 ≤ |Real.sin x| := by
        nlinarith [sq_abs (Real.sin x)]
      have hdiv : Real.sin x ^ 2 / x ≤ |Real.sin x / x| := by
        rw [abs_div, abs_of_pos hxpos]
        exact (div_le_div_iff_of_pos_right hxpos).2 hsq
      exact mul_le_mul_of_nonneg_left hdiv (by norm_num))
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono
  exact tendsto_atTop_mono' atTop hle hscaled

theorem gap17 (p q : ℝ) (hq : 0 < q)
    (hpLower : q - 1 ≤ p) (hpUpper : p < q) :
    ∃ A₀ > 1,
      Tendsto (fun A => ∫ x in A₀..A, absoluteIntegrand p q x)
        atTop atTop := by
  obtain ⟨A₀, hA₀, hpoint⟩ := gap15 p q hq hpLower hpUpper
  refine ⟨A₀, hA₀, ?_⟩
  have hbase := gap16 A₀ hA₀
  have hle : ∀ᶠ A : ℝ in atTop,
      (1 / 3 : ℝ) * (∫ x in A₀..A, |Real.sin x / x|) ≤
        ∫ x in A₀..A, absoluteIntegrand p q x := by
    filter_upwards [eventually_ge_atTop A₀] with A hA
    have hleft : IntervalIntegrable
        (fun x : ℝ => (1 / 3 : ℝ) * |Real.sin x / x|) volume A₀ A := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hA]
      intro x hx
      have hxpos : 0 < x := zero_lt_one.trans (hA₀.trans_le hx.1)
      exact (Real.continuous_sin.continuousAt.div continuousAt_id hxpos.ne').abs.const_mul
        (1 / 3 : ℝ) |>.continuousWithinAt
    have hright : IntervalIntegrable (absoluteIntegrand p q) volume A₀ A := by
      apply ContinuousOn.intervalIntegrable
      exact (continuousOn_integrand_Ioi p q).abs.mono fun x hx => by
        rw [Set.uIcc_of_le hA] at hx
        exact zero_lt_one.trans (hA₀.trans_le hx.1)
    have hmono := intervalIntegral.integral_mono_on hA hleft hright
      (fun x hx => hpoint x hx.1)
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono
  exact tendsto_atTop_mono' atTop hle hbase

theorem gap18 (p : ℝ) (hp : -1 ≤ p) :
    -1 ≤ p := by exact hp

theorem gap19 (p : ℝ) (hp : p < 0) :
    p < 0 := by exact hp

theorem gap20 : (-1 : ℝ) < 0 := by norm_num

theorem gap21 (p A : ℝ) :
    (∫ x in (1 : ℝ)..A, integrand p 0 x) =
      (1 / 2 : ℝ) * ∫ x in (1 : ℝ)..A, Real.rpow x p * Real.sin x := by
  have heq : integrand p 0 =
      fun x : ℝ => (1 / 2 : ℝ) * (Real.rpow x p * Real.sin x) := by
    funext x
    simp only [integrand, weight]
    rw [show Real.rpow x 0 = 1 from Real.rpow_zero x]
    ring
  rw [heq]
  rw [intervalIntegral.integral_const_mul]

private theorem tailConvergent_sin_of_deriv_integrable
    (a : ℝ) (w w' : ℝ → ℝ)
    (hderiv : ∀ x ∈ Set.Ici a, HasDerivAt w (w' x) x)
    (hw' : IntegrableOn w' (Set.Ioi a))
    (hw0 : Tendsto w atTop (nhds 0)) :
    ∃ L : ℝ, Tendsto (fun A => ∫ x in a..A, w x * Real.sin x) atTop (nhds L) := by
  have hprod : IntegrableOn (fun x => w' x * (-Real.cos x)) (Set.Ioi a) := by
    have hcos : AEStronglyMeasurable (fun x : ℝ => -Real.cos x)
        (volume.restrict (Set.Ioi a)) :=
      Real.continuous_cos.neg.stronglyMeasurable.aestronglyMeasurable
    exact hw'.integrable.mul_bdd hcos
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_neg] using Real.abs_cos_le_one x)
  have hid : Tendsto (fun A : ℝ => A) atTop atTop := by
    simpa only [id_eq] using
      (tendsto_id'.2 (show (atTop : Filter ℝ) ≤ atTop from le_rfl))
  have hJ := MeasureTheory.intervalIntegral_tendsto_integral_Ioi
    a hprod hid
  have hboundary : Tendsto (fun A : ℝ => w A * (-Real.cos A)) atTop (nhds 0) := by
    have hmul : Tendsto (fun A : ℝ => (-Real.cos A) * w A) atTop (nhds 0) :=
      bdd_le_mul_tendsto_zero (b := (-1 : ℝ)) (B := (1 : ℝ))
        (Filter.Eventually.of_forall fun x => by linarith [Real.cos_le_one x])
        (Filter.Eventually.of_forall fun x => by linarith [Real.neg_one_le_cos x]) hw0
    simpa only [mul_comm] using hmul
  let L := -(w a * (-Real.cos a)) -
    ∫ x in Set.Ioi a, w' x * (-Real.cos x)
  refine ⟨L, ?_⟩
  have hlim : Tendsto
      (fun A : ℝ => w A * (-Real.cos A) - w a * (-Real.cos a) -
        ∫ x in a..A, w' x * (-Real.cos x)) atTop (nhds L) := by
    simpa only [L, zero_sub] using
      (hboundary.sub tendsto_const_nhds).sub hJ
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop a] with A hA
  have hwcont : ContinuousOn w (Set.uIcc a A) := by
    rw [Set.uIcc_of_le hA]
    intro x hx
    exact (hderiv x (by exact hx.1)).continuousAt.continuousWithinAt
  have hw'int : IntervalIntegrable w' volume a A := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hA]
    exact hw'.mono_set Set.Ioc_subset_Ioi_self
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := a) (b := A) (u := w) (v := fun x => -Real.cos x)
    (u' := w') (v' := Real.sin) hwcont Real.continuous_cos.neg.continuousOn
    (fun x hx => hderiv x (by
      rw [min_eq_left hA, max_eq_right hA] at hx
      exact hx.1.le))
    (fun x _ => by simpa using (Real.hasDerivAt_cos x).neg)
    hw'int (Real.continuous_sin.intervalIntegrable _ _)
  simpa only using hparts.symm

theorem gap22 (p : ℝ) (hpLower : -1 ≤ p) (hpUpper : p < 0) :
    TailConvergent p 0 := by
  let w : ℝ → ℝ := fun x => (1 / 2 : ℝ) * Real.rpow x p
  let w' : ℝ → ℝ := fun x => (p / 2) * Real.rpow x (p - 1)
  have hderiv : ∀ x ∈ Set.Ici (1 : ℝ), HasDerivAt w (w' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
    have hr : HasDerivAt (fun y : ℝ => Real.rpow y p)
        (p * Real.rpow x (p - 1)) x := by
      simpa using Real.hasDerivAt_rpow_const (x := x) (p := p) (Or.inl hx0)
    have hc := hr.const_mul (1 / 2 : ℝ)
    simpa only [w, w'] using hc.congr_deriv (by ring)
  have hw' : IntegrableOn w' (Set.Ioi (1 : ℝ)) := by
    have hr : IntegrableOn (fun x : ℝ => Real.rpow x (p - 1)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    simpa only [w'] using hr.const_mul (p / 2)
  have hw0 : Tendsto w atTop (nhds 0) := by
    have hr : Tendsto (fun x : ℝ => Real.rpow x p) atTop (nhds 0) := by
      convert tendsto_rpow_neg_atTop (show 0 < -p by linarith) using 1 <;> simp
    simpa only [w, mul_zero] using tendsto_const_nhds.mul hr
  obtain ⟨L, hL⟩ := tailConvergent_sin_of_deriv_integrable 1 w w' hderiv hw' hw0
  refine ⟨L, ?_⟩
  apply hL.congr'
  filter_upwards with A
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [integrand, weight, w]
  rw [show Real.rpow x 0 = 1 from Real.rpow_zero x]
  ring

theorem gap23 (p q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    HasDerivAt (weight p q)
      (Real.rpow x (p - 1) *
        (p - (q - p) * Real.rpow x q) / (1 + Real.rpow x q) ^ 2) x := by
  have hp : HasDerivAt (fun y : ℝ => Real.rpow y p)
      (p * Real.rpow x (p - 1)) x := by
    simpa using Real.hasDerivAt_rpow_const (x := x) (p := p) (Or.inl hx.ne')
  have hq' : HasDerivAt (fun y : ℝ => Real.rpow y q)
      (q * Real.rpow x (q - 1)) x := by
    simpa using Real.hasDerivAt_rpow_const (x := x) (p := q) (Or.inl hx.ne')
  have hden : 1 + Real.rpow x q ≠ 0 := by
    have hpow : 0 < Real.rpow x q := by
      simpa using Real.rpow_pos_of_pos hx q
    exact ne_of_gt (by linarith)
  have hquot := hp.div (hasDerivAt_const x 1 |>.add hq') hden
  have hpadd : Real.rpow x p = Real.rpow x (p - 1) * x := by
    calc
      _ = Real.rpow x ((p - 1) + 1) := by congr 1 <;> ring
      _ = Real.rpow x (p - 1) * Real.rpow x 1 := Real.rpow_add hx (p - 1) 1
      _ = _ := by
        have hone : Real.rpow x 1 = x := by simpa using Real.rpow_one x
        rw [hone]
  have hqadd : Real.rpow x q = Real.rpow x (q - 1) * x := by
    calc
      _ = Real.rpow x ((q - 1) + 1) := by congr 1 <;> ring
      _ = Real.rpow x (q - 1) * Real.rpow x 1 := Real.rpow_add hx (q - 1) 1
      _ = _ := by
        have hone : Real.rpow x 1 = x := by simpa using Real.rpow_one x
        rw [hone]
  have hraw : HasDerivAt (weight p q)
      ((p * Real.rpow x (p - 1) * (1 + Real.rpow x q) -
        Real.rpow x p * (q * Real.rpow x (q - 1))) /
        (1 + Real.rpow x q) ^ 2) x := by
    simpa only [weight, Pi.add_apply, Pi.one_apply, Pi.zero_apply, zero_add] using hquot
  have hnum :
      p * Real.rpow x (p - 1) * (1 + Real.rpow x q) -
          Real.rpow x p * (q * Real.rpow x (q - 1)) =
        Real.rpow x (p - 1) * (p - (q - p) * Real.rpow x q) := by
    rw [hpadd]
    calc
      p * Real.rpow x (p - 1) * (1 + Real.rpow x q) -
          (Real.rpow x (p - 1) * x) * (q * Real.rpow x (q - 1)) =
          Real.rpow x (p - 1) *
            (p + p * Real.rpow x q - q * (Real.rpow x (q - 1) * x)) := by ring
      _ = Real.rpow x (p - 1) *
            (p + p * Real.rpow x q - q * Real.rpow x q) := by rw [← hqadd]
      _ = _ := by ring
  exact hraw.congr_deriv (by rw [hnum])

private theorem continuousOn_weight_Ioi (p q : ℝ) :
    ContinuousOn (weight p q) (Set.Ioi 0) := by
  intro x hx
  have hp : ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    Real.continuousAt_rpow_const x p (Or.inl hx.ne')
  have hq : ContinuousAt (fun y : ℝ => Real.rpow y q) x :=
    Real.continuousAt_rpow_const x q (Or.inl hx.ne')
  have hden : 1 + Real.rpow x q ≠ 0 := by
    have hpow : 0 < Real.rpow x q := by
      simpa using Real.rpow_pos_of_pos hx q
    exact ne_of_gt (by linarith)
  exact (hp.div (continuousAt_const.add hq) hden).continuousWithinAt

theorem gap24 (p q : ℝ) (hq : 0 < q) (hpq : p < q) :
    ∃ A₀ > 1, AntitoneOn (weight p q) (Set.Ici A₀) := by
  have hpowTop : Tendsto (fun x : ℝ => Real.rpow x q) atTop atTop := by
    simpa using tendsto_rpow_atTop hq
  have hmulTop : Tendsto (fun x : ℝ => (q - p) * Real.rpow x q) atTop atTop :=
    hpowTop.const_mul_atTop (sub_pos.mpr hpq)
  have hev : ∀ᶠ x : ℝ in atTop, p ≤ (q - p) * Real.rpow x q :=
    hmulTop.eventually (eventually_ge_atTop p)
  obtain ⟨A, hA⟩ := eventually_atTop.1 hev
  let A₀ := max 2 A
  have hA₀ : 1 < A₀ := by
    dsimp only [A₀]
    linarith [le_max_left (2 : ℝ) A]
  refine ⟨A₀, hA₀, ?_⟩
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici A₀)
  · exact (continuousOn_weight_Ioi p q).mono fun x hx =>
      (show 0 < x from lt_trans zero_lt_one (hA₀.trans_le hx))
  · rw [interior_Ici]
    intro x hx
    exact (gap23 p q x hq (lt_trans zero_lt_one (hA₀.trans hx))).hasDerivWithinAt
  · rw [interior_Ici]
    intro x hx
    have hxA : A ≤ x := le_trans (le_max_right (2 : ℝ) A) hx.le
    have hnum : p - (q - p) * Real.rpow x q ≤ 0 := by
      linarith [hA x hxA]
    have hxnonneg : 0 ≤ x := le_trans (by linarith [hA₀] : 0 ≤ A₀) hx.le
    have hpow : 0 ≤ Real.rpow x (p - 1) := Real.rpow_nonneg hxnonneg _
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hpow hnum) (sq_nonneg _)

private theorem tendsto_rpow_div_one_add_rpow (q : ℝ) (hq : 0 < q) :
    Tendsto (fun x : ℝ => Real.rpow x q / (1 + Real.rpow x q)) atTop (nhds 1) := by
  have hqTop : Tendsto (fun x : ℝ => Real.rpow x q) atTop atTop := by
    simpa using tendsto_rpow_atTop hq
  have hdenTop : Tendsto (fun x : ℝ => 1 + Real.rpow x q) atTop atTop :=
    (show Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).add_atTop hqTop
  have hrecip : Tendsto (fun x : ℝ => 1 / (1 + Real.rpow x q)) atTop (nhds 0) :=
    hdenTop.const_div_atTop 1
  have hlim : Tendsto (fun x : ℝ => 1 - 1 / (1 + Real.rpow x q)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hrecip
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hpow : 0 < Real.rpow x q := by
    simpa using Real.rpow_pos_of_pos hx q
  field_simp [ne_of_gt (by linarith : 0 < 1 + Real.rpow x q)]
  ring

theorem gap25 (p q : ℝ) (hq : 0 < q) (hpq : p < q) :
    Tendsto (weight p q) atTop (nhds 0) := by
  have hr : Tendsto (fun x : ℝ => Real.rpow x (p - q)) atTop (nhds 0) := by
    convert tendsto_rpow_neg_atTop (show 0 < q - p by linarith) using 1 <;> simp <;> ring
  have hfactor := tendsto_rpow_div_one_add_rpow q hq
  have hlim : Tendsto
      (fun x : ℝ => Real.rpow x (p - q) *
        (Real.rpow x q / (1 + Real.rpow x q))) atTop (nhds 0) := by
    simpa using hr.mul hfactor
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hadd : Real.rpow x (p - q) * Real.rpow x q = Real.rpow x p := by
    calc
      _ = Real.rpow x ((p - q) + q) := (Real.rpow_add hx (p - q) q).symm
      _ = _ := by congr 1 <;> ring
  simp only [weight]
  rw [show Real.rpow x (p - q) *
      (Real.rpow x q / (1 + Real.rpow x q)) =
      (Real.rpow x (p - q) * Real.rpow x q) /
        (1 + Real.rpow x q) by ring, hadd]

theorem gap26 (A : ℝ) (hA : 1 < A) :
    |∫ x in (1 : ℝ)..A, Real.sin x| ≤ 2 := by
  rw [integral_sin]
  calc
    |Real.cos 1 - Real.cos A| ≤ |Real.cos 1| + |Real.cos A| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one 1) (Real.abs_cos_le_one A)
    _ = 2 := by norm_num

theorem gap27 (p q : ℝ) (hq : 0 < q) (hpq : p < q) :
    TailConvergent p q := by
  obtain ⟨A₀, hA₀, hanti⟩ := gap24 p q hq hpq
  let w' : ℝ → ℝ := fun x => Real.rpow x (p - 1) *
    (p - (q - p) * Real.rpow x q) / (1 + Real.rpow x q) ^ 2
  have hderiv : ∀ x ∈ Set.Ici A₀, HasDerivAt (weight p q) (w' x) x := by
    intro x hx
    exact gap23 p q x hq (lt_trans zero_lt_one (hA₀.trans_le hx))
  have hnonpos : ∀ x ∈ Set.Ioi A₀, w' x ≤ 0 := by
    intro x hx
    have hd : HasDerivWithinAt (weight p q) (w' x) (Set.Ici A₀) x :=
      (hderiv x (by simpa only [Set.mem_Ici] using hx.le)).hasDerivWithinAt
    rw [← hd.derivWithin (uniqueDiffOn_Ici A₀ x
      (by simpa only [Set.mem_Ici] using hx.le))]
    exact hanti.derivWithin_nonpos
  have hw' : IntegrableOn w' (Set.Ioi A₀) :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos' hderiv hnonpos (gap25 p q hq hpq)
  obtain ⟨L, hL⟩ := tailConvergent_sin_of_deriv_integrable
    A₀ (weight p q) w' hderiv hw' (gap25 p q hq hpq)
  have hL' : Tendsto (fun A => ∫ x in A₀..A, integrand p q x) atTop (nhds L) := by
    simpa only [integrand] using hL
  let C := ∫ x in (1 : ℝ)..A₀, integrand p q x
  refine ⟨C + L, ?_⟩
  have hsum : Tendsto (fun A => C + ∫ x in A₀..A, integrand p q x)
      atTop (nhds (C + L)) := tendsto_const_nhds.add hL'
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop A₀] with A hA
  have hfirst : IntervalIntegrable (integrand p q) volume (1 : ℝ) A₀ := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_integrand_Ioi p q).mono fun x hx => by
      rw [Set.uIcc_of_le hA₀.le] at hx
      exact lt_of_lt_of_le zero_lt_one hx.1
  have hsecond : IntervalIntegrable (integrand p q) volume A₀ A := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_integrand_Ioi p q).mono fun x hx => by
      rw [Set.uIcc_of_le hA] at hx
      exact lt_trans zero_lt_one (hA₀.trans_le hx.1)
  dsimp only [C]
  exact intervalIntegral.integral_add_adjacent_intervals hfirst hsecond

private theorem integrableOn_integrand_of_absolute (p q : ℝ) (s : Set ℝ)
    (h : IntegrableOn (absoluteIntegrand p q) s) :
    IntegrableOn (integrand p q) s := by
  have hmeas : AEStronglyMeasurable (integrand p q) (volume.restrict s) :=
    (measurable_integrand p q).aestronglyMeasurable
  change Integrable (integrand p q) (volume.restrict s)
  apply (integrable_norm_iff hmeas).mp
  change Integrable (absoluteIntegrand p q) (volume.restrict s) at h
  simpa only [absoluteIntegrand, Real.norm_eq_abs] using h

private theorem tailConvergent_of_integrableOn (p q : ℝ)
    (h : IntegrableOn (integrand p q) (Set.Ioi (1 : ℝ))) :
    TailConvergent p q := by
  refine ⟨∫ x in Set.Ioi (1 : ℝ), integrand p q x, ?_⟩
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 h tendsto_id

private theorem tailConvergent_iff_lt (p q : ℝ) (hq : 0 ≤ q) :
    TailConvergent p q ↔ p < q := by
  constructor
  · intro htail
    by_contra hpq
    exact gap7 p q hq (le_of_not_gt hpq) htail
  · intro hpq
    rcases hq.eq_or_lt with rfl | hqpos
    · by_cases hp : p < -1
      · have habs : TailAbsolutelyIntegrable p 0 := gap13 p 0 le_rfl (by linarith)
        exact tailConvergent_of_integrableOn p 0
          (integrableOn_integrand_of_absolute p 0 (Set.Ioi (1 : ℝ)) habs)
      · exact gap22 p (le_of_not_gt hp) hpq
    · exact gap27 p q hqpos hpq

private theorem fullConvergent_iff_bounds (p q : ℝ) (hq : 0 ≤ q) :
    FullConvergent p q ↔ -2 < p ∧ p < q := by
  unfold FullConvergent
  rw [gap4 p q hq, tailConvergent_iff_lt p q hq]

private theorem absoluteIntegral_q_zero_tendsto_atTop (p : ℝ) (hp : -1 ≤ p) :
    Tendsto (fun A => ∫ x in (2 : ℝ)..A, absoluteIntegrand p 0 x) atTop atTop := by
  have hbase := gap16 2 (by norm_num)
  have hle : ∀ᶠ A : ℝ in atTop,
      (1 / 3 : ℝ) * (∫ x in (2 : ℝ)..A, |Real.sin x / x|) ≤
        ∫ x in (2 : ℝ)..A, absoluteIntegrand p 0 x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
    have hleft : IntervalIntegrable
        (fun x : ℝ => (1 / 3 : ℝ) * |Real.sin x / x|) volume 2 A := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hA]
      intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      exact (Real.continuous_sin.continuousAt.div continuousAt_id hxpos.ne').abs.const_mul
        (1 / 3 : ℝ) |>.continuousWithinAt
    have hright : IntervalIntegrable (absoluteIntegrand p 0) volume 2 A := by
      apply ContinuousOn.intervalIntegrable
      exact (continuousOn_integrand_Ioi p 0).abs.mono fun x hx => by
        rw [Set.uIcc_of_le hA] at hx
        exact (by norm_num : (0 : ℝ) < 2) |>.trans_le hx.1
    have hmono := intervalIntegral.integral_mono_on hA hleft hright (fun x hx => by
      have hxone : 1 ≤ x := by linarith [hx.1]
      have hxpos : 0 < x := zero_lt_one.trans_le hxone
      have hpow : Real.rpow x (-1 : ℝ) ≤ Real.rpow x p :=
        Real.rpow_le_rpow_of_exponent_le hxone hp
      have hinv : Real.rpow x (-1 : ℝ) = x⁻¹ := by
        simpa only using Real.rpow_neg_one x
      have hpPos : 0 < Real.rpow x p := Real.rpow_pos_of_pos hxpos p
      have hs : 0 ≤ |Real.sin x| := abs_nonneg _
      have hcoef : (1 / 3 : ℝ) * x⁻¹ ≤ (1 / 2 : ℝ) * Real.rpow x p := by
        rw [← hinv]
        nlinarith [Real.rpow_nonneg hxpos.le (-1 : ℝ)]
      have hsinc : |Real.sin x / x| = |Real.sin x| * x⁻¹ := by
        rw [abs_div, abs_of_pos hxpos]
        simp only [div_eq_mul_inv]
      rw [hsinc]
      unfold absoluteIntegrand integrand weight
      have hz : Real.rpow x 0 = 1 := Real.rpow_zero x
      rw [hz]
      rw [abs_mul, abs_of_pos (div_pos hpPos (by norm_num : (0 : ℝ) < 1 + 1))]
      have := mul_le_mul_of_nonneg_right hcoef hs
      nlinarith)
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono
  exact tendsto_atTop_mono' atTop hle hbase

theorem gap28 (p q : ℝ) (hq : 0 ≤ q) :
    FullAbsolutelyIntegrable p q ↔
      -2 < p ∧ p + 1 < q := by
  constructor
  · intro habs
    have hnearAbs : IntegrableOn (absoluteIntegrand p q) (Set.Ioc (0 : ℝ) 1) :=
      habs.mono Set.Ioc_subset_Ioi_self le_rfl
    have hnear : NearZeroIntegrable p q :=
      integrableOn_integrand_of_absolute p q (Set.Ioc (0 : ℝ) 1) hnearAbs
    have hpLower : -2 < p := (gap4 p q hq).mp hnear
    refine ⟨hpLower, ?_⟩
    by_contra hpq
    have hqle : q ≤ p + 1 := le_of_not_gt hpq
    have htailAbs : IntegrableOn (absoluteIntegrand p q) (Set.Ioi (1 : ℝ)) :=
      habs.mono (Set.Ioi_subset_Ioi zero_le_one) le_rfl
    by_cases hqp : q ≤ p
    · have htail : TailConvergent p q := tailConvergent_of_integrableOn p q
        (integrableOn_integrand_of_absolute p q (Set.Ioi (1 : ℝ)) htailAbs)
      exact gap7 p q hq hqp htail
    · have hpq' : p < q := lt_of_not_ge hqp
      rcases hq.eq_or_lt with hqzero | hqpos
      · subst q
        have hpneg : p < 0 := hpq'
        have hpge : -1 ≤ p := by linarith
        have hdiv := absoluteIntegral_q_zero_tendsto_atTop p hpge
        have htail2 : IntegrableOn (absoluteIntegrand p 0) (Set.Ioi (2 : ℝ)) :=
          htailAbs.mono (Set.Ioi_subset_Ioi (by norm_num)) le_rfl
        have hfinite := MeasureTheory.intervalIntegral_tendsto_integral_Ioi
          2 htail2 tendsto_id
        exact (not_tendsto_atTop_of_tendsto_nhds hfinite) hdiv
      · have hpLower' : q - 1 ≤ p := by linarith
        obtain ⟨A₀, hA₀, hdiv⟩ := gap17 p q hqpos hpLower' hpq'
        have htailA : IntegrableOn (absoluteIntegrand p q) (Set.Ioi A₀) :=
          htailAbs.mono (Set.Ioi_subset_Ioi hA₀.le) le_rfl
        have hfinite := MeasureTheory.intervalIntegral_tendsto_integral_Ioi
          A₀ htailA tendsto_id
        exact (not_tendsto_atTop_of_tendsto_nhds hfinite) hdiv
  · rintro ⟨hp, hpq⟩
    have hnear : NearZeroIntegrable p q := (gap4 p q hq).mpr hp
    have hnearAbs : IntegrableOn (absoluteIntegrand p q) (Set.Ioc (0 : ℝ) 1) := by
      have h := hnear.norm
      simpa only [absoluteIntegrand, Real.norm_eq_abs] using h
    have htail : TailAbsolutelyIntegrable p q := gap13 p q hq (by linarith)
    unfold FullAbsolutelyIntegrable
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hnearAbs.union htail

theorem gap29 (p q : ℝ) (hq : 0 ≤ q) :
    (FullConvergent p q ∧ ¬ FullAbsolutelyIntegrable p q) ↔
      (-2 < p ∧ p < q ∧ q ≤ p + 1) := by
  rw [fullConvergent_iff_bounds p q hq, gap28 p q hq]
  constructor
  · rintro ⟨⟨hp, hpq⟩, hnabs⟩
    refine ⟨hp, hpq, ?_⟩
    by_contra hle
    exact hnabs ⟨hp, lt_of_not_ge hle⟩
  · rintro ⟨hp, hpq, hqle⟩
    refine ⟨⟨hp, hpq⟩, ?_⟩
    rintro ⟨_, habs⟩
    linarith

theorem gap30 (p q : ℝ) (hq : 0 ≤ q) :
    (-2 < p ∧ p < q) ↔ FullConvergent p q := by
  exact (fullConvergent_iff_bounds p q hq).symm

end
end ProofGap.Exercise2381
