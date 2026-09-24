import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3737

noncomputable section

open Filter
open scoped Interval Topology

def quotient (a b x : ℝ) : ℝ :=
  (Real.rpow x b - Real.rpow x a) / Real.log x

def lHopitalQuotient (a b x : ℝ) : ℝ :=
  (b * Real.rpow x (b - 1) - a * Real.rpow x (a - 1)) / x⁻¹

def simplifiedLimitFunction (a b x : ℝ) : ℝ :=
  b * Real.rpow x b - a * Real.rpow x a

def powerIntegral (a b x : ℝ) : ℝ :=
  ∫ y in a..b, Real.rpow x y

def originalIntegral (a b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, quotient a b x

private theorem one_rpow_explicit (p : ℝ) : Real.rpow 1 p = 1 := by
  change (1 : ℝ) ^ p = 1
  rw [Real.rpow_def_of_pos (show (0 : ℝ) < 1 by norm_num) p]
  norm_num

private theorem rpow_eq_exp_log (x y : ℝ) (hx : 0 < x) :
    Real.rpow x y = Real.exp (y * Real.log x) := by
  change x ^ y = Real.exp (y * Real.log x)
  simpa only [mul_comm] using (Real.rpow_def_of_pos hx y)

private theorem quotient_tendsto_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (quotient a b) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := inf_le_left
  have hrpow (p : ℝ) (hp : 0 < p) :
      Tendsto (fun x : ℝ => Real.rpow x p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => Real.rpow x p) 0 :=
      continuousAt_id.rpow continuousAt_const (Or.inr hp)
    have ht := hc.tendsto.mono_left hle
    have hz : Real.rpow 0 p = 0 := by
      change (0 : ℝ) ^ p = 0
      exact Real.zero_rpow (ne_of_gt hp)
    simpa only [hz] using ht
  have hlog : Tendsto (fun x : ℝ => (Real.log x)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hnum := (hrpow b hb).sub (hrpow a ha)
  simpa [quotient, div_eq_mul_inv] using hnum.mul hlog

private theorem quotient_tendsto_one (a b : ℝ) :
    Tendsto (quotient a b) (𝓝[<] (1 : ℝ)) (𝓝 (b - a)) := by
  have hbder : HasDerivAt (fun x : ℝ => Real.rpow x b) b 1 := by
    simpa [one_rpow_explicit] using
      Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := b)
        (Or.inl one_ne_zero)
  have hader : HasDerivAt (fun x : ℝ => Real.rpow x a) a 1 := by
    simpa [one_rpow_explicit] using
      Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := a)
        (Or.inl one_ne_zero)
  have hnum : HasDerivAt
      (fun x : ℝ => Real.rpow x b - Real.rpow x a) (b - a) 1 :=
    hbder.sub hader
  have hlog : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)
  have hsnum := hasDerivAt_iff_tendsto_slope.mp hnum
  have hslog := hasDerivAt_iff_tendsto_slope.mp hlog
  have hs : Tendsto
      (fun x => slope (fun z : ℝ => Real.rpow z b - Real.rpow z a) 1 x /
        slope Real.log 1 x)
      (𝓝[≠] (1 : ℝ)) (𝓝 (b - a)) := by
    simpa using hsnum.div hslog (by norm_num)
  have hfilter : 𝓝[<] (1 : ℝ) ≤ 𝓝[≠] (1 : ℝ) := by
    apply nhdsWithin_mono
    intro x hx
    simpa only [Set.mem_Iio, Set.mem_compl_iff, Set.mem_singleton_iff] using
      ne_of_lt hx
  have hnhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) := inf_le_left
  have hpos : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), 0 < x :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono hnhds
  refine (hs.mono_left hfilter).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hpos] with x hx hxpos
  have hne : x ≠ 1 := ne_of_lt hx
  have hxm : -1 + x ≠ 0 := by
    intro hzero
    apply hne
    linarith
  have hloglt : Real.log x < 0 := Real.log_neg hxpos hx
  have hlogne : Real.log x ≠ 0 := ne_of_lt hloglt
  have hcancel : (-1 + x) * (-1 + x)⁻¹ = (1 : ℝ) := by
    exact mul_inv_cancel₀ hxm
  simp only [slope, quotient, one_rpow_explicit, Real.log_one, sub_self,
    sub_zero, vsub_eq_sub, smul_eq_mul]
  field_simp [hne, hxm, hlogne]
  calc
    _ = ((-1 + x) * (-1 + x)⁻¹) *
        (Real.rpow x b - Real.rpow x a) := by ring
    _ = Real.rpow x b - Real.rpow x a := by
      simp only [hcancel, one_mul]

private theorem simplified_tendsto_one (a b : ℝ) :
    Tendsto (simplifiedLimitFunction a b) (𝓝[<] (1 : ℝ))
      (𝓝 (b - a)) := by
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) := inf_le_left
  have hp (p : ℝ) : Tendsto (fun x : ℝ => Real.rpow x p)
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => Real.rpow x p) 1 :=
      continuousAt_id.rpow continuousAt_const (Or.inl one_ne_zero)
    simpa only [one_rpow_explicit] using hc.tendsto.mono_left hle
  have hbconst : Tendsto (fun _ : ℝ => b) (𝓝[<] (1 : ℝ)) (𝓝 b) :=
    tendsto_const_nhds
  have haconst : Tendsto (fun _ : ℝ => a) (𝓝[<] (1 : ℝ)) (𝓝 a) :=
    tendsto_const_nhds
  simpa [simplifiedLimitFunction] using
    (hbconst.mul (hp b)).sub (haconst.mul (hp a))

private theorem lHopital_tendsto_one (a b : ℝ) :
    Tendsto (lHopitalQuotient a b) (𝓝[<] (1 : ℝ))
      (𝓝 (b - a)) := by
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) := inf_le_left
  have hp (p : ℝ) : Tendsto (fun x : ℝ => Real.rpow x p)
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => Real.rpow x p) 1 :=
      continuousAt_id.rpow continuousAt_const (Or.inl one_ne_zero)
    simpa only [one_rpow_explicit] using hc.tendsto.mono_left hle
  have hbconst : Tendsto (fun _ : ℝ => b) (𝓝[<] (1 : ℝ)) (𝓝 b) :=
    tendsto_const_nhds
  have haconst : Tendsto (fun _ : ℝ => a) (𝓝[<] (1 : ℝ)) (𝓝 a) :=
    tendsto_const_nhds
  have hbterm : Tendsto (fun x : ℝ => b * Real.rpow x (b - 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (b * 1)) := hbconst.mul (hp (b - 1))
  have hatterm : Tendsto (fun x : ℝ => a * Real.rpow x (a - 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (a * 1)) := haconst.mul (hp (a - 1))
  have hnum : Tendsto
      (fun x : ℝ => b * Real.rpow x (b - 1) - a * Real.rpow x (a - 1))
      (𝓝[<] (1 : ℝ)) (𝓝 (b - a)) := by
    simpa using hbterm.sub hatterm
  have hden : Tendsto (fun x : ℝ => x⁻¹)
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => x⁻¹) 1 :=
      continuousAt_id.inv₀ one_ne_zero
    simpa using hc.tendsto.mono_left hle
  simpa [lHopitalQuotient] using hnum.div hden (by norm_num)

theorem gap1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (quotient a b) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact quotient_tendsto_zero a b ha hb

theorem gap2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (quotient a b) (𝓝[<] (1 : ℝ)) (𝓝 (b - a)) ↔
      Tendsto (lHopitalQuotient a b) (𝓝[<] (1 : ℝ)) (𝓝 (b - a)) := by
  constructor
  · intro _
    exact lHopital_tendsto_one a b
  · intro _
    exact quotient_tendsto_one a b

theorem gap3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (lHopitalQuotient a b) (𝓝[<] (1 : ℝ)) (𝓝 (b - a)) ↔
      Tendsto (simplifiedLimitFunction a b) (𝓝[<] (1 : ℝ))
        (𝓝 (b - a)) := by
  constructor
  · intro _
    exact simplified_tendsto_one a b
  · intro _
    exact lHopital_tendsto_one a b

theorem gap4 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (simplifiedLimitFunction a b) (𝓝[<] (1 : ℝ))
      (𝓝 (b - a)) := by
  exact simplified_tendsto_one a b

theorem gap5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (quotient a b) (𝓝[<] (1 : ℝ)) (𝓝 (b - a)) := by
  exact quotient_tendsto_one a b

theorem gap6 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    quotient a b x = powerIntegral a b x := by
  have hloglt : Real.log x < 0 := Real.log_neg hx.1 hx.2
  have hlog : Real.log x ≠ 0 := ne_of_lt hloglt
  have hrpow (y : ℝ) :
      Real.rpow x y = Real.exp (y * Real.log x) :=
    rpow_eq_exp_log x y hx.1
  have hcont : Continuous (fun y : ℝ => Real.rpow x y) := by
    have heq : (fun y : ℝ => Real.rpow x y) =
        fun y : ℝ => Real.exp (y * Real.log x) := by
      funext y
      exact hrpow y
    rw [heq]
    have hm : Continuous (fun y : ℝ => y * Real.log x) :=
      continuous_id.mul continuous_const
    simpa only [Function.comp_apply] using Real.continuous_exp.comp hm
  have hderiv : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => Real.exp (z * Real.log x) / Real.log x)
        (Real.rpow x y) y := by
    intro y
    have hd : HasDerivAt
        (fun z : ℝ => Real.exp (z * Real.log x) / Real.log x)
        (Real.exp (y * Real.log x) * (1 * Real.log x) / Real.log x) y := by
      simpa only [id_eq] using
        (((hasDerivAt_id y).mul_const (Real.log x)).exp.div_const
          (Real.log x))
    have heq :
        Real.exp (y * Real.log x) * (1 * Real.log x) / Real.log x =
          Real.rpow x y := by
      rw [hrpow y]
      field_simp [hlog]
    simpa only [heq] using hd
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hderiv y) (hcont.intervalIntegrable a b)
  change (Real.rpow x b - Real.rpow x a) / Real.log x =
    ∫ y in a..b, Real.rpow x y
  rw [hrpow b, hrpow a]
  calc
    (Real.exp (b * Real.log x) - Real.exp (a * Real.log x)) /
        Real.log x =
      Real.exp (b * Real.log x) / Real.log x -
        Real.exp (a * Real.log x) / Real.log x := by ring
    _ = ∫ y in a..b, Real.rpow x y := hi.symm

theorem gap7 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    originalIntegral a b =
      ∫ x in (0 : ℝ)..1, powerIntegral a b x := by
  have hne : ∀ᵐ x : ℝ
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.Ioc (0 : ℝ) 1)), x ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  rw [originalIntegral, intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
    intervalIntegral.integral_of_le (le_of_lt zero_lt_one)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
    hne] with x hx hx1
  exact gap6 a b x ha hb ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..1, powerIntegral a b x) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..1, Real.rpow x y := by
  have hordered (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
      (∫ x in (0 : ℝ)..1, powerIntegral c d x) =
        ∫ y in c..d, ∫ x in (0 : ℝ)..1, Real.rpow x y := by
    let f : ℝ × ℝ → ℝ := fun p => Real.rpow p.1 p.2
    have hcont : ContinuousOn f
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d) := by
      intro p hp
      have hp2 : 0 < p.2 := lt_of_lt_of_le hc hp.2.1
      exact (continuous_fst.continuousAt.rpow continuous_snd.continuousAt
        (by
          by_cases hp1 : p.1 = 0
          · exact Or.inr hp2
          · exact Or.inl hp1)).continuousWithinAt
    have hintClosed : MeasureTheory.IntegrableOn f
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
      hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hsub : Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d ⊆
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c d := by
      apply Set.prod_mono
      · intro x hx
        exact ⟨le_of_lt hx.1, hx.2⟩
      · intro y hy
        exact ⟨le_of_lt hy.1, hy.2⟩
    have hintOpen : MeasureTheory.IntegrableOn f
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
      hintClosed.mono_set hsub
    have hmeas : MeasurableSet
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d) :=
      measurableSet_Ioc.prod measurableSet_Ioc
    have hind : MeasureTheory.Integrable
        ((Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d).indicator f)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
      rw [MeasureTheory.integrable_indicator_iff hmeas]
      exact hintOpen
    let g : ℝ → ℝ → ℝ := fun x y =>
      (Set.Ioc (0 : ℝ) 1).indicator
        (fun x => (Set.Ioc c d).indicator
          (fun y => Real.rpow x y) y) x
    have huncurry : Function.uncurry g =
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc c d).indicator f := by
      funext p
      by_cases hx : p.1 ∈ Set.Ioc (0 : ℝ) 1
      · by_cases hy : p.2 ∈ Set.Ioc c d
        · simp [Function.uncurry, g, f, hx, hy]
        · simp [Function.uncurry, g, f, hx, hy]
      · simp [Function.uncurry, g, f, hx]
    have hg : MeasureTheory.Integrable (Function.uncurry g)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
      rw [huncurry]
      exact hind
    have hswap :
        (∫ x : ℝ, ∫ y : ℝ, g x y
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ y : ℝ, ∫ x : ℝ, g x y
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      MeasureTheory.integral_integral_swap hg
    have hleft :
        (∫ x : ℝ, ∫ y : ℝ, g x y
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ x in Set.Ioc (0 : ℝ) 1,
            ∫ y in Set.Ioc c d, Real.rpow x y := by
      calc
        (∫ x : ℝ, ∫ y : ℝ, g x y
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
            ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
              (fun x => ∫ y : ℝ, (Set.Ioc c d).indicator
                (fun y => Real.rpow x y) y
                ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) x
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
          · simp [g, hx]
          · simp [g, hx]
        _ = ∫ x in Set.Ioc (0 : ℝ) 1,
              ∫ y : ℝ, (Set.Ioc c d).indicator
                (fun y => Real.rpow x y) y
                ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          exact MeasureTheory.integral_indicator measurableSet_Ioc
        _ = ∫ x in Set.Ioc (0 : ℝ) 1,
              ∫ y in Set.Ioc c d, Real.rpow x y := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          exact MeasureTheory.integral_indicator measurableSet_Ioc
    have hright :
        (∫ y : ℝ, ∫ x : ℝ, g x y
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
          ∫ y in Set.Ioc c d,
            ∫ x in Set.Ioc (0 : ℝ) 1, Real.rpow x y := by
      calc
        (∫ y : ℝ, ∫ x : ℝ, g x y
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
            ∫ y : ℝ, (Set.Ioc c d).indicator
              (fun y => ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
                (fun x => Real.rpow x y) x
                ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) y
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with y
          by_cases hy : y ∈ Set.Ioc c d
          · simp [g, hy]
          · simp [g, hy]
        _ = ∫ y in Set.Ioc c d,
              ∫ x : ℝ, (Set.Ioc (0 : ℝ) 1).indicator
                (fun x => Real.rpow x y) x
                ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          exact MeasureTheory.integral_indicator measurableSet_Ioc
        _ = ∫ y in Set.Ioc c d,
              ∫ x in Set.Ioc (0 : ℝ) 1, Real.rpow x y := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with y
          exact MeasureTheory.integral_indicator measurableSet_Ioc
    simpa only [powerIntegral,
      intervalIntegral.integral_of_le (le_of_lt zero_lt_one),
      intervalIntegral.integral_of_le hcd] using
        hleft.symm.trans (hswap.trans hright)
  rcases le_total a b with hab | hba
  · exact hordered a b ha hab
  · have hswap := hordered b a hb hba
    calc
      (∫ x in (0 : ℝ)..1, powerIntegral a b x) =
          ∫ x in (0 : ℝ)..1, -powerIntegral b a x := by
        apply intervalIntegral.integral_congr
        intro x _
        unfold powerIntegral
        rw [intervalIntegral.integral_symm]
      _ = -(∫ x in (0 : ℝ)..1, powerIntegral b a x) := by
        rw [intervalIntegral.integral_neg]
      _ = -(∫ y in b..a, ∫ x in (0 : ℝ)..1, Real.rpow x y) :=
        congrArg Neg.neg hswap
      _ = ∫ y in a..b, ∫ x in (0 : ℝ)..1, Real.rpow x y := by
        have hsymm :
            (∫ y in b..a, ∫ x in (0 : ℝ)..1, Real.rpow x y) =
              -(∫ y in a..b, ∫ x in (0 : ℝ)..1, Real.rpow x y) := by
          rw [intervalIntegral.integral_symm]
        calc
          -(∫ y in b..a, ∫ x in (0 : ℝ)..1, Real.rpow x y) =
              -(-(∫ y in a..b, ∫ x in (0 : ℝ)..1, Real.rpow x y)) :=
            congrArg Neg.neg hsymm
          _ = ∫ y in a..b, ∫ x in (0 : ℝ)..1, Real.rpow x y := neg_neg _

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, ∫ x in (0 : ℝ)..1, Real.rpow x y) =
      ∫ y in a..b, 1 / (1 + y) := by
  apply intervalIntegral.integral_congr
  intro y hy
  have hypos : 0 < y := by
    rcases Set.mem_uIcc.mp hy with h | h
    · exact lt_of_lt_of_le ha h.1
    · exact lt_of_lt_of_le hb h.1
  have hy1 : y + 1 ≠ 0 := by linarith
  have hy1' : 1 + y ≠ 0 := by linarith
  have hcont : ContinuousOn (fun x : ℝ => Real.rpow x y)
      (Set.uIcc (0 : ℝ) 1) := by
    intro x hx
    exact (continuousAt_id.rpow continuousAt_const
      (by
        by_cases hzero : x = 0
        · exact Or.inr hypos
        · exact Or.inl hzero)).continuousWithinAt
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun z : ℝ => Real.rpow z (y + 1) / (y + 1))
        (Real.rpow x y) x := by
    intro x
    have hd := (Real.hasDerivAt_rpow_const (x := x) (p := y + 1)
      (Or.inr (by linarith))).div_const (y + 1)
    simpa [show y + 1 - 1 = y by ring, hy1] using hd
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hcont.intervalIntegrable
  have hone : Real.rpow 1 (y + 1) = 1 := one_rpow_explicit (y + 1)
  have hzero : Real.rpow 0 (y + 1) = 0 := by
    change (0 : ℝ) ^ (y + 1) = 0
    exact Real.zero_rpow (ne_of_gt (by linarith))
  calc
    (∫ x in (0 : ℝ)..1, Real.rpow x y) =
        Real.rpow 1 (y + 1) / (y + 1) -
          Real.rpow 0 (y + 1) / (y + 1) := hi
    _ = 1 / (1 + y) := by
      rw [hone, hzero]
      field_simp [hy1, hy1'] <;> ring

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, 1 / (1 + y)) =
      Real.log ((1 + b) / (1 + a)) := by
  have hpos : ∀ y ∈ Set.uIcc a b, 0 < 1 + y := by
    intro y hy
    rcases Set.mem_uIcc.mp hy with h | h
    · linarith [ha, h.1]
    · linarith [hb, h.1]
  have hcont : ContinuousOn (fun y : ℝ => 1 / (1 + y))
      (Set.uIcc a b) := by
    intro y hy
    have hne : 1 + y ≠ 0 := ne_of_gt (hpos y hy)
    simpa only [one_div] using
      ((continuousAt_const.add continuousAt_id).inv₀ hne).continuousWithinAt
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun z : ℝ => Real.log (1 + z)) (1 / (1 + y)) y := by
    intro y hy
    have hne : 1 + y ≠ 0 := ne_of_gt (hpos y hy)
    have hin := (hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)
    have hd := (Real.hasDerivAt_log hne).comp y hin
    convert hd using 1 <;>
      simp only [one_div, zero_add, mul_one]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  calc
    (∫ y in a..b, 1 / (1 + y)) =
        Real.log (1 + b) - Real.log (1 + a) := hi
    _ = Real.log ((1 + b) / (1 + a)) := by
      rw [Real.log_div (ne_of_gt (by linarith : 0 < 1 + b))
        (ne_of_gt (by linarith : 0 < 1 + a))]

theorem gap11 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    originalIntegral a b = Real.log ((1 + b) / (1 + a)) := by
  calc
    originalIntegral a b =
        ∫ x in (0 : ℝ)..1, powerIntegral a b x := gap7 a b ha hb
    _ = ∫ y in a..b, ∫ x in (0 : ℝ)..1, Real.rpow x y := gap8 a b ha hb
    _ = ∫ y in a..b, 1 / (1 + y) := gap9 a b ha hb
    _ = Real.log ((1 + b) / (1 + a)) := gap10 a b ha hb

end

end ProofGap.Exercise3737
