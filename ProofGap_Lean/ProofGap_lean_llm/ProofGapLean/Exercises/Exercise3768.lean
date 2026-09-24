import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3768

noncomputable section

open Filter Set MeasureTheory
open scoped Interval Topology

def originalIntegrand (n x : ℝ) : ℝ :=
  Real.sin (1 / x) / Real.rpow x n

def transformedIntegrand (n t : ℝ) : ℝ :=
  Real.rpow t (n - 2) * Real.sin t

def lowerEndpoint (m : ℕ) : ℝ :=
  2 * (m : ℝ) * Real.pi + Real.pi / 4

def upperEndpoint (m : ℕ) : ℝ :=
  2 * (m : ℝ) * Real.pi + Real.pi / 2

def HasImproperTailValue (n A L : ℝ) : Prop :=
  Tendsto (fun B : ℝ => ∫ t in A..B, transformedIntegrand n t)
    atTop (nhds L)

def UniformTailConvergence : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A₀ : ℝ, 1 < A₀ ∧
      ∀ A n L : ℝ, A₀ < A → n ∈ Set.Ioo (0 : ℝ) 2 →
        HasImproperTailValue n A L → |L| < ε

private def boundary (n x : ℝ) : ℝ :=
  Real.rpow x (2 - n) * Real.cos (1 / x)

private def remainder (n x : ℝ) : ℝ :=
  (2 - n) * (Real.rpow x (1 - n) * Real.cos (1 / x))

private theorem boundary_deriv (n x : ℝ) (hx : 0 < x) :
    HasDerivAt (boundary n)
      (remainder n x + originalIntegrand n x) x := by
  have hpow := Real.hasDerivAt_rpow_const
    (x := x) (p := 2 - n) (Or.inl hx.ne')
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
    simpa [one_div] using hasDerivAt_inv hx.ne'
  have hcos := (Real.hasDerivAt_cos (1 / x)).comp x hinv
  have h := hpow.mul hcos
  convert h using 1
  · simp only [Function.comp_apply]
    unfold remainder originalIntegrand
    change
      (2 - n) * (Real.rpow x (1 - n) * Real.cos (1 / x)) +
          Real.sin (1 / x) / Real.rpow x n =
        (2 - n) * Real.rpow x (2 - n - 1) * Real.cos (1 / x) +
          Real.rpow x (2 - n) *
            (-Real.sin (1 / x) * (-(x ^ 2)⁻¹))
    have hxpow : Real.rpow x (2 - n) =
        Real.rpow x (1 - n) * x := by
      simpa only [show 2 - n = (1 - n) + 1 by ring] using
        Real.rpow_add_one hx.ne' (1 - n)
    have hxpow2 : Real.rpow x (2 - n) =
        x ^ 2 / Real.rpow x n := by
      simpa only [Real.rpow_two] using Real.rpow_sub hx 2 n
    rw [show 2 - n - 1 = 1 - n by ring, hxpow2]
    field_simp [hx.ne', ne_of_gt (Real.rpow_pos_of_pos hx n)]

private theorem remainder_intervalIntegrable (n : ℝ) (hn : n < 2) :
    IntervalIntegrable (remainder n) volume 0 1 := by
  have hexp : -(1 : ℝ) < 1 - n := by linarith
  have hpow : IntervalIntegrable
      (fun x : ℝ => Real.rpow x (1 - n)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  have hmeas : Measurable (fun x : ℝ => Real.cos (1 / x)) :=
    Real.measurable_cos.comp (measurable_const.div measurable_id)
  have hbound : ∀ x : ℝ, ‖Real.cos (1 / x)‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hmul : IntervalIntegrable
      (fun x : ℝ => Real.rpow x (1 - n) * Real.cos (1 / x))
      volume 0 1 := by
    constructor
    · simpa only [mul_comm] using
        hpow.1.bdd_mul hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall hbound)
    · simpa only [mul_comm] using
        hpow.2.bdd_mul hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall hbound)
  exact hmul.const_mul (2 - n)

private theorem finite_formula (n a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x in a..1, originalIntegrand n x) =
      boundary n 1 - boundary n a - ∫ x in a..1, remainder n x := by
  have hcontF :
      ContinuousOn (fun x => originalIntegrand n x) (uIcc a 1) := by
    intro x hx
    have hxI : x ∈ Icc a 1 := by simpa [uIcc, ha1] using hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hxI.1
    have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
      simpa [one_div] using hasDerivAt_inv hx0.ne'
    have hsin := (Real.hasDerivAt_sin (1 / x)).comp x hinv
    have hpow := Real.hasDerivAt_rpow_const
      (x := x) (p := n) (Or.inl hx0.ne')
    exact (hsin.continuousAt.div hpow.continuousAt
      (ne_of_gt (Real.rpow_pos_of_pos hx0 _))).continuousWithinAt
  have hcontR : ContinuousOn (remainder n) (uIcc a 1) := by
    intro x hx
    have hxI : x ∈ Icc a 1 := by simpa [uIcc, ha1] using hx
    have hx0 := lt_of_lt_of_le ha hxI.1
    have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
      simpa [one_div] using hasDerivAt_inv hx0.ne'
    have hcos := (Real.hasDerivAt_cos (1 / x)).comp x hinv
    have hpow := Real.hasDerivAt_rpow_const
      (x := x) (p := 1 - n) (Or.inl hx0.ne')
    simpa only [remainder, Function.comp_apply] using
      (continuousAt_const.mul
        (hpow.continuousAt.mul hcos.continuousAt)).continuousWithinAt
  have hfint :
      IntervalIntegrable (fun x => originalIntegrand n x) volume a 1 :=
    hcontF.intervalIntegrable
  have hrint : IntervalIntegrable (remainder n) volume a 1 :=
    hcontR.intervalIntegrable
  have hsum := hrint.add hfint
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := 1)
    (fun x hx => boundary_deriv n x (by
      have hxI : x ∈ Icc a 1 := by simpa [uIcc, ha1] using hx
      exact lt_of_lt_of_le ha hxI.1))
    hsum
  rw [intervalIntegral.integral_add hrint hfint] at hFTC
  linarith

private theorem boundary_tendsto_zero (n : ℝ) (hn : n < 2) :
    Tendsto (boundary n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : 0 < 2 - n := by linarith
  have hpowCont :
      ContinuousAt (fun x : ℝ => Real.rpow x (2 - n)) 0 :=
    continuousAt_id.rpow continuousAt_const (Or.inr hp)
  have hpowZero : Real.rpow 0 (2 - n) = 0 :=
    Real.zero_rpow hp.ne'
  have hpow :
      Tendsto (fun x : ℝ => Real.rpow x (2 - n))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hpowZero] using hpowCont.tendsto.mono_left inf_le_left
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      |boundary n x| ≤ Real.rpow x (2 - n) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hpowNonneg : 0 ≤ Real.rpow x (2 - n) :=
      Real.rpow_nonneg hxpos.le _
    rw [boundary, abs_mul, abs_of_nonneg hpowNonneg]
    exact mul_le_of_le_one_right hpowNonneg (Real.abs_cos_le_one _)
  apply (tendsto_zero_iff_abs_tendsto_zero (boundary n)).2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x => abs_nonneg _
  · simpa only [Function.comp_apply] using hbound
  · exact hpow

private theorem remainder_integral_tendsto (n : ℝ) (hn : n < 2) :
    Tendsto (fun a => ∫ x in a..1, remainder n x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in (0 : ℝ)..1, remainder n x)) := by
  have hr := remainder_intervalIntegrable n hn
  have hron : IntegrableOn (remainder n) (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 hr
  have hcont : ContinuousOn
      (fun a => ∫ x in a..1, remainder n x) (uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval_left (by
      simpa [uIcc, zero_le_one] using hron)
  have hzero : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := left_mem_uIcc
  have ht := (hcont 0 hzero).tendsto
  apply ht.mono_left
  apply le_inf
  · exact inf_le_left
  · rw [le_principal_iff]
    have hlt : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a < 1 := by
      exact Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hlt] with a ha0 ha1
    simpa [uIcc, zero_le_one] using
      (show a ∈ Icc (0 : ℝ) 1 from ⟨ha0.le, ha1.le⟩)

private theorem pointwise_converges (n : ℝ) (hn : n < 2) :
    ∃ L : ℝ,
      Tendsto
        (fun a => ∫ x in a..1, originalIntegrand n x)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let L : ℝ := boundary n 1 - ∫ x in (0 : ℝ)..1, remainder n x
  refine ⟨L, ?_⟩
  have hb := boundary_tendsto_zero n hn
  have hr := remainder_integral_tendsto n hn
  have ht :
      Tendsto
        (fun a => boundary n 1 - boundary n a -
          ∫ x in a..1, remainder n x)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa [L] using (tendsto_const_nhds.sub hb).sub hr
  apply ht.congr'
  have hlt : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a < 1 := by
    exact Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, hlt] with a ha0 ha1
  exact (finite_formula n a ha0 ha1.le).symm

private theorem pos_of_mem_recip_uIcc
    {δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ uIcc (1 : ℝ) (1 / δ)) :
    0 < t := by
  rw [Set.mem_uIcc] at ht
  rcases ht with ht | ht
  · exact zero_lt_one.trans_le ht.1
  · exact (one_div_pos.mpr hδ).trans_le ht.1

private theorem finite_reciprocal_transform
    (n δ : ℝ) (hδ : 0 < δ) :
    (∫ x in δ..1, originalIntegrand n x) =
      ∫ t in (1 : ℝ)..(1 / δ), transformedIntegrand n t := by
  let invf : ℝ → ℝ := fun t => 1 / t
  let invf' : ℝ → ℝ := fun t => -1 / t ^ 2
  have hinv :
      ∀ t ∈ uIcc (1 : ℝ) (1 / δ),
        HasDerivAt invf (invf' t) t := by
    intro t ht
    have htpos := pos_of_mem_recip_uIcc hδ ht
    convert hasDerivAt_inv htpos.ne' using 1 <;>
      simp [invf, invf', one_div, div_eq_mul_inv]
  have hinv' :
      ContinuousOn invf' (uIcc (1 : ℝ) (1 / δ)) := by
    intro t ht
    have htpos := pos_of_mem_recip_uIcc hδ ht
    dsimp [invf']
    exact
      (continuousAt_const.div (continuousAt_id.pow 2)
        (pow_ne_zero 2 htpos.ne')).continuousWithinAt
  have horig :
      ContinuousOn (originalIntegrand n)
        (invf '' uIcc (1 : ℝ) (1 / δ)) := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    have htpos := pos_of_mem_recip_uIcc hδ ht
    have hypos : 0 < invf t := by
      dsimp [invf]
      positivity
    have hinvy :
        HasDerivAt (fun z : ℝ => 1 / z) (-((invf t) ^ 2)⁻¹) (invf t) := by
      simpa [one_div] using hasDerivAt_inv hypos.ne'
    have hsin := (Real.hasDerivAt_sin (1 / invf t)).comp (invf t) hinvy
    have hpow := Real.hasDerivAt_rpow_const
      (x := invf t) (p := n) (Or.inl hypos.ne')
    exact
      (hsin.continuousAt.div hpow.continuousAt
        (ne_of_gt (Real.rpow_pos_of_pos hypos n))).continuousWithinAt
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'
      (a := (1 : ℝ)) (b := 1 / δ)
      (f := invf) (f' := invf') (g := originalIntegrand n)
      hinv hinv' horig
  have hpoint :
      ∀ t ∈ uIcc (1 : ℝ) (1 / δ),
        (originalIntegrand n ∘ invf) t * invf' t =
          -transformedIntegrand n t := by
    intro t ht
    have htpos := pos_of_mem_recip_uIcc hδ ht
    have hinvinv : 1 / (1 / t) = t := by
      field_simp [htpos.ne']
    have hrinv :
        Real.rpow (1 / t) n = (Real.rpow t n)⁻¹ := by
      simpa only [one_div] using Real.inv_rpow htpos.le n
    have hrsub :
        Real.rpow t (n - 2) =
          Real.rpow t n / t ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_sub htpos n 2
    dsimp [invf, invf']
    unfold originalIntegrand transformedIntegrand
    rw [hinvinv, hrinv, hrsub]
    field_simp [htpos.ne', ne_of_gt (Real.rpow_pos_of_pos htpos n)]
  have hleft :
      (∫ t in (1 : ℝ)..(1 / δ),
        (originalIntegrand n ∘ invf) t * invf' t) =
        -(∫ t in (1 : ℝ)..(1 / δ), transformedIntegrand n t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    exact hpoint
  have hright :
      (∫ x in (1 : ℝ)..δ, originalIntegrand n x) =
        -(∫ x in δ..1, originalIntegrand n x) := by
    rw [intervalIntegral.integral_symm]
  have hinvδ : 1 / (1 / δ) = δ := by
    field_simp [hδ.ne']
  dsimp [invf] at hsub
  rw [show (1 / (1 : ℝ)) = 1 by norm_num,
    hinvδ] at hsub
  dsimp [invf] at hleft
  rw [hleft, hright] at hsub
  linarith

theorem gap1 (n L : ℝ) :
    Tendsto
        (fun δ : ℝ => ∫ x in δ..1, originalIntegrand n x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ↔
      Tendsto
        (fun A : ℝ => ∫ t in (1 : ℝ)..A, transformedIntegrand n t)
        atTop (nhds L) := by
  constructor
  · intro h
    have hcomp :=
      h.comp (show Tendsto (fun A : ℝ => 1 / A) atTop (𝓝[>] (0 : ℝ)) by
        simpa [one_div] using
          (tendsto_inv_atTop_nhdsGT_zero :
            Tendsto (fun A : ℝ => A⁻¹) atTop (𝓝[>] (0 : ℝ))))
    apply hcomp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    have heq := finite_reciprocal_transform n (1 / A) (one_div_pos.mpr hA)
    simpa [one_div_div, hA.ne'] using heq
  · intro h
    have hcomp :=
      h.comp (show Tendsto (fun δ : ℝ => 1 / δ)
          (𝓝[>] (0 : ℝ)) atTop by
        simpa [one_div] using
          (tendsto_inv_nhdsGT_zero :
            Tendsto (fun δ : ℝ => δ⁻¹) (𝓝[>] (0 : ℝ)) atTop))
    apply hcomp.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (finite_reciprocal_transform n δ hδ).symm

theorem gap2 (n : ℝ) (hn : n < 2) :
    ∃ L : ℝ,
      Tendsto
        (fun A : ℝ => ∫ t in (1 : ℝ)..A, transformedIntegrand n t)
        atTop (nhds L) := by
  obtain ⟨L, hL⟩ := pointwise_converges n hn
  exact ⟨L, (gap1 n L).1 hL⟩

private theorem lowerEndpoint_pos (m : ℕ) :
    0 < lowerEndpoint m := by
  unfold lowerEndpoint
  have hpi := Real.pi_pos
  positivity

private theorem lowerEndpoint_lt_upperEndpoint (m : ℕ) :
    lowerEndpoint m < upperEndpoint m := by
  unfold lowerEndpoint upperEndpoint
  linarith [Real.pi_pos]

private theorem upperEndpoint_pos (m : ℕ) :
    0 < upperEndpoint m :=
  (lowerEndpoint_pos m).trans (lowerEndpoint_lt_upperEndpoint m)

private theorem sin_lower_bound
    (m : ℕ) (t : ℝ)
    (ht : t ∈ Icc (lowerEndpoint m) (upperEndpoint m)) :
    Real.sqrt 2 / 2 ≤ Real.sin t := by
  let y : ℝ := t - 2 * (m : ℝ) * Real.pi
  have hylo : Real.pi / 4 ≤ y := by
    dsimp [y]
    unfold lowerEndpoint at ht
    linarith [ht.1]
  have hyhi : y ≤ Real.pi / 2 := by
    dsimp [y]
    unfold upperEndpoint at ht
    linarith [ht.2]
  have hpi4mem :
      Real.pi / 4 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hymem :
      y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact ⟨(by nlinarith [Real.pi_pos, hylo]), hyhi⟩
  have hperiod : Real.sin t = Real.sin y := by
    calc
      Real.sin t =
          Real.sin (y + (m : ℝ) * (2 * Real.pi)) := by
        congr 1
        dsimp [y]
        ring
      _ = Real.sin y := by
        simpa using Real.sin_add_nat_mul_two_pi y m
  rw [hperiod, ← Real.sin_pi_div_four]
  exact Real.monotoneOn_sin hpi4mem hymem hylo

private theorem sin_upperEndpoint (m : ℕ) :
    Real.sin (upperEndpoint m) = 1 := by
  calc
    Real.sin (upperEndpoint m) =
        Real.sin (Real.pi / 2 + (m : ℝ) * (2 * Real.pi)) := by
      congr 1
      unfold upperEndpoint
      ring
    _ = Real.sin (Real.pi / 2) := by
      simpa using Real.sin_add_nat_mul_two_pi (Real.pi / 2) m
    _ = 1 := Real.sin_pi_div_two

private theorem transformed_eq_weight
    (n t : ℝ) (ht : 0 < t) :
    transformedIntegrand n t =
      (1 / Real.rpow t (2 - n)) * Real.sin t := by
  unfold transformedIntegrand
  rw [show n - 2 = -(2 - n) by ring]
  have hneg :
      Real.rpow t (-(2 - n)) =
        (Real.rpow t (2 - n))⁻¹ := by
    simpa using Real.rpow_neg ht.le (2 - n)
  rw [hneg]
  simp [one_div]

private theorem weight_continuousOn
    (p a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => 1 / Real.rpow t p) (Icc a b) := by
  intro t ht
  have htpos : 0 < t := ha.trans_le ht.1
  exact
    (continuousAt_const.div
      (Real.hasDerivAt_rpow_const
        (x := t) (p := p) (Or.inl htpos.ne')).continuousAt
      (ne_of_gt (Real.rpow_pos_of_pos htpos p))).continuousWithinAt

private theorem transformed_continuousOn
    (n a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (transformedIntegrand n) (Icc a b) := by
  intro t ht
  have htpos : 0 < t := ha.trans_le ht.1
  unfold transformedIntegrand
  exact
    ((Real.hasDerivAt_rpow_const
      (x := t) (p := n - 2) (Or.inl htpos.ne')).continuousAt.mul
      Real.continuous_sin.continuousAt).continuousWithinAt

theorem gap3 (n : ℝ) (m : ℕ) (hm : 0 < m) :
    (∫ t in lowerEndpoint m..upperEndpoint m,
        transformedIntegrand n t) >
      Real.sqrt 2 / 2 *
        ∫ t in lowerEndpoint m..upperEndpoint m,
          1 / Real.rpow t (2 - n) := by
  let a := lowerEndpoint m
  let b := upperEndpoint m
  let c : ℝ := Real.sqrt 2 / 2
  let w : ℝ → ℝ := fun t => 1 / Real.rpow t (2 - n)
  have ha : 0 < a := lowerEndpoint_pos m
  have hab : a < b := lowerEndpoint_lt_upperEndpoint m
  have hw : ContinuousOn w (Icc a b) := by
    exact weight_continuousOn (2 - n) a b ha hab.le
  have htrans :
      ContinuousOn (transformedIntegrand n) (Icc a b) :=
    transformed_continuousOn n a b ha hab.le
  have hle :
      ∀ t ∈ Ioc a b, c * w t ≤ transformedIntegrand n t := by
    intro t ht
    dsimp [c, w]
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have htpos : 0 < t := ha.trans ht.1
    rw [transformed_eq_weight n t htpos]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left
        (sin_lower_bound m t htI) (le_of_lt (one_div_pos.mpr
          (Real.rpow_pos_of_pos htpos (2 - n)))))
  have hstrict :
      ∃ t ∈ Icc a b, c * w t < transformedIntegrand n t := by
    refine ⟨b, right_mem_Icc.mpr hab.le, ?_⟩
    dsimp [c, w]
    have hbpos : 0 < b := ha.trans hab
    rw [transformed_eq_weight n b hbpos, sin_upperEndpoint m]
    have hc : Real.sqrt 2 / 2 < 1 := by
      nlinarith [Real.sqrt_two_lt_three_halves]
    simpa [mul_comm] using
      (mul_lt_mul_of_pos_right hc
        (one_div_pos.mpr (Real.rpow_pos_of_pos hbpos (2 - n))))
  have hlt :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hab (continuous_const.continuousOn.mul hw) htrans hle hstrict
  change
    (∫ t in a..b, transformedIntegrand n t) >
      c * ∫ t in a..b, w t
  rw [← intervalIntegral.integral_const_mul]
  exact hlt

theorem gap4 (n : ℝ) (m : ℕ) (hn : n < 2) (hm : 0 < m) :
    (∫ t in lowerEndpoint m..upperEndpoint m,
        transformedIntegrand n t) >
      Real.sqrt 2 / 2 * (Real.pi / 4) *
        (1 / Real.rpow (upperEndpoint m) (2 - n)) := by
  let a := lowerEndpoint m
  let b := upperEndpoint m
  let p : ℝ := 2 - n
  let c : ℝ := Real.sqrt 2 / 2
  let w : ℝ → ℝ := fun t => 1 / Real.rpow t p
  have ha : 0 < a := lowerEndpoint_pos m
  have hab : a < b := lowerEndpoint_lt_upperEndpoint m
  have hp : 0 < p := by dsimp [p]; linarith
  have hb : 0 < b := ha.trans hab
  have hw : IntervalIntegrable w volume a b :=
    by
      apply ContinuousOn.intervalIntegrable
      dsimp [w]
      simpa [uIcc, hab.le, one_div] using
        (weight_continuousOn p a b ha hab.le)
  have hconst :
      IntervalIntegrable (fun _ : ℝ => w b) volume a b :=
    continuous_const.intervalIntegrable _ _
  have hpoint :
      ∀ t ∈ Icc a b, w b ≤ w t := by
    intro t ht
    have htpos : 0 < t := ha.trans_le ht.1
    have hpow :=
      Real.rpow_le_rpow htpos.le ht.2 hp.le
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos htpos p) hpow
  have hint :
      (∫ _ in a..b, w b) ≤
        ∫ t in a..b, w t :=
    intervalIntegral.integral_mono_on hab.le hconst hw hpoint
  have hconstValue :
      (∫ _ in a..b, w b) =
        (Real.pi / 4) * w b := by
    rw [intervalIntegral.integral_const]
    dsimp [a, b]
    unfold lowerEndpoint upperEndpoint
    ring
  rw [hconstValue] at hint
  have hbasic := gap3 n m hm
  change
    c * (Real.pi / 4) * w b <
      ∫ t in a..b, transformedIntegrand n t
  change
    c * (∫ t in a..b, w t) <
      ∫ t in a..b, transformedIntegrand n t at hbasic
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hscaled := (mul_le_mul_of_nonneg_left hint hc).trans_lt hbasic
  convert hscaled using 1 <;> ring

theorem gap5 (m : ℕ) (hm : 0 < m) :
    Tendsto
      (fun n : ℝ => 1 / Real.rpow (upperEndpoint m) (2 - n))
      (nhdsWithin 2 (Set.Iio 2)) (nhds 1) := by
  have hb : 0 < upperEndpoint m := upperEndpoint_pos m
  have hc :
      Continuous
        (fun n : ℝ => 1 / Real.rpow (upperEndpoint m) (2 - n)) := by
    apply Continuous.div continuous_const
    · exact
        (Real.continuous_const_rpow hb.ne').comp
          (continuous_const.sub continuous_id)
    · intro n
      exact ne_of_gt (Real.rpow_pos_of_pos hb (2 - n))
  have ht :
      Tendsto
        (fun n : ℝ => 1 / Real.rpow (upperEndpoint m) (2 - n))
        (𝓝[<] (2 : ℝ))
        (𝓝 (1 / Real.rpow (upperEndpoint m) (2 - (2 : ℝ)))) :=
    hc.continuousAt.tendsto.mono_left inf_le_left
  simpa using ht

theorem gap6 (m : ℕ) (hm : 0 < m) :
    ∃ n ∈ Set.Ioo (0 : ℝ) 2,
      Real.sqrt 2 * Real.pi / 16 <
        ∫ t in lowerEndpoint m..upperEndpoint m,
          transformedIntegrand n t := by
  have ht := gap5 m hm
  have hrecip :
      ∀ᶠ n : ℝ in 𝓝[<] (2 : ℝ),
        (1 / 2 : ℝ) <
          1 / Real.rpow (upperEndpoint m) (2 - n) :=
    (tendsto_order.1 ht).1 (1 / 2 : ℝ) (by norm_num)
  have hpositive :
      ∀ᶠ n : ℝ in 𝓝[<] (2 : ℝ), 0 < n := by
    exact Filter.Eventually.filter_mono inf_le_left
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨n, ⟨hnrecip, hn2⟩, hn0⟩ :=
    (hrecip.and self_mem_nhdsWithin |>.and hpositive).exists
  refine ⟨n, ⟨hn0, hn2⟩, ?_⟩
  have hlarge := gap4 n m hn2 hm
  let coeff : ℝ := Real.sqrt 2 / 2 * (Real.pi / 4)
  have hcoeff : 0 < coeff := by
    dsimp [coeff]
    positivity
  have hmul :
      coeff * (1 / 2 : ℝ) <
        coeff *
          (1 / Real.rpow (upperEndpoint m) (2 - n)) :=
    mul_lt_mul_of_pos_left hnrecip hcoeff
  calc
    Real.sqrt 2 * Real.pi / 16 = coeff * (1 / 2 : ℝ) := by
      dsimp [coeff]
      ring
    _ < coeff * (1 / Real.rpow (upperEndpoint m) (2 - n)) := hmul
    _ < ∫ t in lowerEndpoint m..upperEndpoint m,
        transformedIntegrand n t := by
      dsimp [coeff]
      exact hlarge

private theorem transformed_intervalIntegrable
    (n a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (transformedIntegrand n) volume a b := by
  apply ContinuousOn.intervalIntegrable
  simpa [uIcc, hab] using
    (transformed_continuousOn n a b ha hab)

private theorem prefix_limit_gives_tail
    (n A L : ℝ) (hA : 1 < A)
    (hprefix :
      Tendsto
        (fun B : ℝ => ∫ t in (1 : ℝ)..B, transformedIntegrand n t)
        atTop (𝓝 L)) :
    HasImproperTailValue n A
      (L - ∫ t in (1 : ℝ)..A, transformedIntegrand n t) := by
  have hlim :=
    hprefix.sub
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℝ => ∫ t in (1 : ℝ)..A, transformedIntegrand n t)
          atTop
          (𝓝 (∫ t in (1 : ℝ)..A, transformedIntegrand n t)))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop A] with B hB
  have h1A :=
    transformed_intervalIntegrable n 1 A zero_lt_one hA.le
  have hAB :=
    transformed_intervalIntegrable n A B (zero_lt_one.trans hA) hB.le
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h1A hAB
  linarith

theorem gap7 :
    ¬ UniformTailConvergence := by
  intro huniform
  let ε : ℝ := Real.sqrt 2 * Real.pi / 32
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨A₀, hA₀, htailSmall⟩ := huniform ε hε
  let q : ℝ :=
    max 0 ((A₀ - Real.pi / 4) / (2 * Real.pi))
  obtain ⟨m : ℕ, hmgt⟩ := exists_nat_gt q
  have hmR : 0 < (m : ℝ) := by
    exact (le_max_left 0 ((A₀ - Real.pi / 4) / (2 * Real.pi))).trans_lt hmgt
  have hm : 0 < m := by exact_mod_cast hmR
  have hratio :
      (A₀ - Real.pi / 4) / (2 * Real.pi) < (m : ℝ) :=
    (le_max_right 0 ((A₀ - Real.pi / 4) / (2 * Real.pi))).trans_lt hmgt
  have hcross :
      A₀ - Real.pi / 4 < (m : ℝ) * (2 * Real.pi) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).1 hratio
  have hlower : A₀ < lowerEndpoint m := by
    calc
      A₀ < (m : ℝ) * (2 * Real.pi) + Real.pi / 4 := by
        linarith
      _ = lowerEndpoint m := by
        unfold lowerEndpoint
        ring
  have hupper : A₀ < upperEndpoint m :=
    hlower.trans (lowerEndpoint_lt_upperEndpoint m)
  obtain ⟨n, hn, hsegmentLarge⟩ := gap6 m hm
  obtain ⟨L, hprefix⟩ := gap2 n hn.2
  let P : ℝ → ℝ :=
    fun B => ∫ t in (1 : ℝ)..B, transformedIntegrand n t
  let LA : ℝ := L - P (lowerEndpoint m)
  let LU : ℝ := L - P (upperEndpoint m)
  have hlowOne : 1 < lowerEndpoint m := hA₀.trans hlower
  have hupOne : 1 < upperEndpoint m := hA₀.trans hupper
  have htailA : HasImproperTailValue n (lowerEndpoint m) LA := by
    dsimp [LA, P]
    exact prefix_limit_gives_tail n (lowerEndpoint m) L hlowOne hprefix
  have htailU : HasImproperTailValue n (upperEndpoint m) LU := by
    dsimp [LU, P]
    exact prefix_limit_gives_tail n (upperEndpoint m) L hupOne hprefix
  have hLA : |LA| < ε :=
    htailSmall (lowerEndpoint m) n LA hlower hn htailA
  have hLU : |LU| < ε :=
    htailSmall (upperEndpoint m) n LU hupper hn htailU
  have h1lower :=
    transformed_intervalIntegrable n 1 (lowerEndpoint m)
      zero_lt_one hlowOne.le
  have hlowerUpper :=
    transformed_intervalIntegrable n (lowerEndpoint m) (upperEndpoint m)
      (lowerEndpoint_pos m) (lowerEndpoint_lt_upperEndpoint m).le
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      h1lower hlowerUpper
  have hsegmentEq :
      (∫ t in lowerEndpoint m..upperEndpoint m,
        transformedIntegrand n t) = LA - LU := by
    dsimp [LA, LU, P]
    linarith
  have hsegmentAbs :
      |∫ t in lowerEndpoint m..upperEndpoint m,
        transformedIntegrand n t| < 2 * ε := by
    rw [hsegmentEq]
    calc
      |LA - LU| ≤ |LA| + |LU| := abs_sub LA LU
      _ < ε + ε := add_lt_add hLA hLU
      _ = 2 * ε := by ring
  have htwo :
      2 * ε = Real.sqrt 2 * Real.pi / 16 := by
    dsimp [ε]
    ring
  rw [htwo] at hsegmentAbs
  have hlargeAbs :
      Real.sqrt 2 * Real.pi / 16 <
        |∫ t in lowerEndpoint m..upperEndpoint m,
          transformedIntegrand n t| :=
    hsegmentLarge.trans_le (le_abs_self _)
  exact (lt_asymm hlargeAbs hsegmentAbs)

theorem gap8 :
    ¬ UniformTailConvergence := by
  exact gap7

end

end ProofGap.Exercise3768
