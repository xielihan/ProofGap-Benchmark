import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4135

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def solid (p : ℝ) : Set Point3 :=
  {q |
    0 ≤ q.1 ∧ q.1 ≤ p / 2 ∧
      -Real.sqrt (2 * p * q.1) ≤ q.2.1 ∧
      q.2.1 ≤ Real.sqrt (2 * p * q.1) ∧
        0 ≤ q.2.2 ∧ q.2.2 ≤ q.1 ^ 2 / (2 * p)}

def mass (p : ℝ) : ℝ :=
  ∫ _q in solid p, (1 : ℝ)

def xCentroid (p : ℝ) : ℝ :=
  1 / mass p * ∫ q in solid p, q.1

def yCentroid (p : ℝ) : ℝ :=
  1 / mass p * ∫ q in solid p, q.2.1

def zCentroid (p : ℝ) : ℝ :=
  1 / mass p * ∫ q in solid p, q.2.2

private theorem explicit_rpow_eq_pow_of_nonneg (x a : ℝ) (hx : 0 ≤ x) :
    Real.rpow x a = x ^ a := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · simp [Real.rpow_def_of_pos hx]

private theorem integral_rpow_of_two_le (c b : ℝ) (hc : 2 ≤ c) (hb : 0 ≤ b) :
    (∫ x in (0 : ℝ)..b, Real.rpow x (c - 1)) =
      (1 / c) * Real.rpow b c := by
  have hc0 : c ≠ 0 := by linarith
  have hcm1one : 1 ≤ c - 1 := by linarith
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) b) :
      HasDerivAt (fun t : ℝ => (1 / c) * Real.rpow t c)
        (Real.rpow x (c - 1)) x := by
    rw [Set.uIcc_of_le hb] at hx
    have hx0 : 0 ≤ x := hx.1
    convert (Real.hasDerivAt_rpow_const (p := c)
      (Or.inr (by linarith : 1 ≤ c))).const_mul (1 / c) using 1
    rw [explicit_rpow_eq_pow_of_nonneg x (c - 1) hx0]
    field_simp [hc0]
  have hcont : Continuous (fun x : ℝ => Real.rpow x (c - 1)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (Real.hasDerivAt_rpow_const (p := c - 1) (Or.inr hcm1one)).continuousAt
  calc
    (∫ x in (0 : ℝ)..b, Real.rpow x (c - 1)) =
        (1 / c) * Real.rpow b c - (1 / c) * Real.rpow 0 c :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hderiv x hx) (hcont.intervalIntegrable (0 : ℝ) b)
    _ = (1 / c) * Real.rpow b c := by simp [hc0]

private theorem solid_subset_bounding_box (p : ℝ) (hp : 0 < p) :
    solid p ⊆
      Set.Icc (0 : ℝ) (p / 2) ×ˢ
        (Set.Icc (-p) p ×ˢ Set.Icc (0 : ℝ) p) := by
  intro q hq
  rcases hq with ⟨hx0, hxp, hyl, hyu, hz0, hzu⟩
  have hpx : 0 ≤ p * (p / 2 - q.1) :=
    mul_nonneg hp.le (sub_nonneg.mpr hxp)
  have hrad : 0 ≤ 2 * p * q.1 := by positivity
  have hsquare : (Real.sqrt (2 * p * q.1)) ^ 2 = 2 * p * q.1 :=
    Real.sq_sqrt hrad
  have hsqrtle : Real.sqrt (2 * p * q.1) ≤ p := by
    have hsqrt0 := Real.sqrt_nonneg (2 * p * q.1)
    nlinarith
  have hfrac : q.1 ^ 2 / (2 * p) ≤ p := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * p)).2
    nlinarith [sq_nonneg (p / 2 - q.1)]
  refine ⟨⟨hx0, hxp⟩, ⟨⟨?_, ?_⟩, ⟨hz0, ?_⟩⟩⟩
  · exact le_trans (neg_le_neg hsqrtle) hyl
  · exact le_trans hyu hsqrtle
  · exact le_trans hzu hfrac

private theorem bounding_box_compact (p : ℝ) :
    IsCompact
      (Set.Icc (0 : ℝ) (p / 2) ×ˢ
        (Set.Icc (-p) p ×ˢ Set.Icc (0 : ℝ) p)) := by
  exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

private theorem integral_solid_eq_iterated
    (p : ℝ) (hp : 0 < p) (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ q in solid p, f q) =
      ∫ x in (0 : ℝ)..p / 2,
        ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
          ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), f (x, y, z) := by
  classical
  have hs : MeasurableSet (solid p) := by
    unfold solid
    measurability
  have hbox :
      IntegrableOn f
        (Set.Icc (0 : ℝ) (p / 2) ×ˢ
          (Set.Icc (-p) p ×ˢ Set.Icc (0 : ℝ) p)) volume :=
    hf.continuousOn.integrableOn_compact (bounding_box_compact p)
  have hfi : IntegrableOn f (solid p) volume :=
    hbox.mono_set (solid_subset_bounding_box p hp)
  have hind : Integrable ((solid p).indicator f) volume :=
    (integrable_indicator_iff hs).2 hfi
  change Integrable ((solid p).indicator f)
    (volume.prod (volume.prod volume)) at hind
  have hprod :
      (∫ q : Point3, (solid p).indicator f q ∂volume.prod (volume.prod volume)) =
        ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          (solid p).indicator f (x, y, z) := by
    rw [MeasureTheory.integral_prod _ hind]
    apply integral_congr_ae
    filter_upwards [hind.prod_right_ae] with x hx
    change
      (∫ yz : ℝ × ℝ, (solid p).indicator f (x, yz) ∂volume.prod volume) =
        ∫ y : ℝ, ∫ z : ℝ, (solid p).indicator f (x, y, z)
    rw [MeasureTheory.integral_prod _ hx]
  have hsections :
      (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        (solid p).indicator f (x, y, z)) =
        ∫ x in Set.Icc (0 : ℝ) (p / 2),
          ∫ y in Set.Icc (-Real.sqrt (2 * p * x)) (Real.sqrt (2 * p * x)),
            ∫ z in Set.Icc (0 : ℝ) (x ^ 2 / (2 * p)), f (x, y, z) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) (p / 2)
    · rw [Set.indicator_of_mem hx]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Set.Icc (-Real.sqrt (2 * p * x)) (Real.sqrt (2 * p * x))
      · rw [Set.indicator_of_mem hy]
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ Set.Icc (0 : ℝ) (x ^ 2 / (2 * p))
        · have hsolid : (x, y, z) ∈ solid p :=
            ⟨hx.1, hx.2, hy.1, hy.2, hz.1, hz.2⟩
          simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hsolid]
        · have hnsolid : (x, y, z) ∉ solid p := by
            intro hq
            rcases hq with ⟨hx0, hxp, hyl, hyu, hz0, hzu⟩
            exact hz ⟨hz0, hzu⟩
          have hzr :
              (Set.Icc (0 : ℝ) (x ^ 2 / (2 * p))).indicator
                (fun z => f (x, y, z)) z = 0 := by
            simp [Set.indicator, hz]
          have hzl : (solid p).indicator f (x, y, z) = 0 := by
            simp [Set.indicator, hnsolid]
          rw [hzl, hzr]
      · have hyr :
            (Set.Icc (-Real.sqrt (2 * p * x)) (Real.sqrt (2 * p * x))).indicator
              (fun y => ∫ z in Set.Icc (0 : ℝ) (x ^ 2 / (2 * p)), f (x, y, z)) y = 0 := by
          simp [Set.indicator, hy]
        rw [hyr, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with z
        have hnsolid : (x, y, z) ∉ solid p := by
          intro hq
          rcases hq with ⟨hx0, hxp, hyl, hyu, hz0, hzu⟩
          exact hy ⟨hyl, hyu⟩
        simp [Set.indicator, hnsolid]
    · have hxr :
          (Set.Icc (0 : ℝ) (p / 2)).indicator
            (fun x =>
              ∫ y in Set.Icc (-Real.sqrt (2 * p * x)) (Real.sqrt (2 * p * x)),
                ∫ z in Set.Icc (0 : ℝ) (x ^ 2 / (2 * p)), f (x, y, z)) x = 0 := by
        simp [Set.indicator, hx]
      rw [hxr, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with z
      have hnsolid : (x, y, z) ∉ solid p := by
        intro hq
        rcases hq with ⟨hx0, hxp, hyl, hyu, hz0, hzu⟩
        exact hx ⟨hx0, hxp⟩
      simp [Set.indicator, hnsolid]
  have hp2 : 0 ≤ p / 2 := by positivity
  calc
    (∫ q in solid p, f q) =
        ∫ q : Point3, (solid p).indicator f q := by
      rw [MeasureTheory.integral_indicator hs]
    _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          (solid p).indicator f (x, y, z) := hprod
    _ = ∫ x in Set.Icc (0 : ℝ) (p / 2),
          ∫ y in Set.Icc (-Real.sqrt (2 * p * x)) (Real.sqrt (2 * p * x)),
            ∫ z in Set.Icc (0 : ℝ) (x ^ 2 / (2 * p)), f (x, y, z) := hsections
    _ = ∫ x in (0 : ℝ)..p / 2,
          ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), f (x, y, z) := by
      rw [intervalIntegral.integral_of_le hp2]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      have hyorder :
          -Real.sqrt (2 * p * x) ≤ Real.sqrt (2 * p * x) := by
        exact neg_le_self (Real.sqrt_nonneg _)
      rw [intervalIntegral.integral_of_le hyorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      dsimp only
      have hzorder : 0 ≤ x ^ 2 / (2 * p) := by positivity
      rw [intervalIntegral.integral_of_le hzorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem gap1 (p : ℝ) (hp : 0 < p) :
    mass p =
      ∫ x in (0 : ℝ)..p / 2,
        ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
          ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ) := by
  unfold mass
  simpa using
    integral_solid_eq_iterated p hp (fun _q : Point3 => (1 : ℝ))
      (continuous_const : Continuous (fun _q : Point3 => (1 : ℝ)))

theorem gap2 (p : ℝ) (hp : 0 < p) :
    (∫ x in (0 : ℝ)..p / 2,
        ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
          ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) =
      Real.sqrt (2 / p) *
        ∫ x in (0 : ℝ)..p / 2, Real.rpow x ((5 : ℝ) / 2) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  have hp2 : 0 ≤ p / 2 := by positivity
  rw [Set.uIcc_of_le hp2] at hx
  have hx0 : 0 ≤ x := hx.1
  have h2px : 0 ≤ 2 * p * x := by positivity
  have h2p : 0 ≤ 2 / p := by positivity
  have hr : Real.rpow x ((5 : ℝ) / 2) = x ^ 2 * Real.sqrt x := by
    by_cases hzero : x = 0
    · simp [hzero]
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hzero)
      calc
        Real.rpow x ((5 : ℝ) / 2) =
            Real.rpow x ((2 : ℝ) + 1 / 2) := by norm_num
        _ = Real.rpow x (2 : ℝ) * Real.rpow x ((1 : ℝ) / 2) := by
          exact Real.rpow_add hxpos _ _
        _ = x ^ 2 * Real.sqrt x := by
          norm_num [Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hsquare :
      (Real.sqrt (2 / p) * Real.sqrt x * p) ^ 2 =
        (Real.sqrt (2 * p * x)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt h2p, Real.sq_sqrt hx0,
      Real.sq_sqrt h2px]
    field_simp [hp0]
  have hleft : 0 ≤ Real.sqrt (2 / p) * Real.sqrt x * p := by positivity
  have hright : 0 ≤ Real.sqrt (2 * p * x) := Real.sqrt_nonneg _
  have hs : Real.sqrt (2 / p) * Real.sqrt x * p = Real.sqrt (2 * p * x) := by
    nlinarith [hsquare]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
  rw [hr, ← hs]
  field_simp [hp0] <;> ring

theorem gap3 (p : ℝ) (hp : 0 < p) :
    Real.sqrt (2 / p) *
        (∫ x in (0 : ℝ)..p / 2, Real.rpow x ((5 : ℝ) / 2)) =
      p ^ 3 / 28 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp2 : 0 < p / 2 := by positivity
  have hi :
      (∫ x in (0 : ℝ)..p / 2, Real.rpow x ((5 : ℝ) / 2)) =
        (2 / 7 : ℝ) * Real.rpow (p / 2) ((7 : ℝ) / 2) := by
    convert integral_rpow_of_two_le ((7 : ℝ) / 2) (p / 2) (by norm_num) hp2.le using 1 <;>
      norm_num
  rw [hi]
  have hr :
      Real.rpow (p / 2) ((7 : ℝ) / 2) =
        (p / 2) ^ 3 * Real.sqrt (p / 2) := by
    calc
      Real.rpow (p / 2) ((7 : ℝ) / 2) =
          Real.rpow (p / 2) ((3 : ℝ) + 1 / 2) := by norm_num
      _ = Real.rpow (p / 2) (3 : ℝ) * Real.rpow (p / 2) ((1 : ℝ) / 2) := by
        exact Real.rpow_add hp2 _ _
      _ = (p / 2) ^ 3 * Real.sqrt (p / 2) := by
        norm_num [Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [hr]
  have hA : 0 ≤ 2 / p := by positivity
  have hB : 0 ≤ p / 2 := hp2.le
  have hsquare :
      (Real.sqrt (2 / p) * Real.sqrt (p / 2)) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    field_simp [hp0]
  have hnonneg : 0 ≤ Real.sqrt (2 / p) * Real.sqrt (p / 2) := by positivity
  have hs : Real.sqrt (2 / p) * Real.sqrt (p / 2) = 1 := by
    nlinarith [hsquare]
  calc
    Real.sqrt (2 / p) * ((2 / 7 : ℝ) * ((p / 2) ^ 3 * Real.sqrt (p / 2))) =
        (2 / 7 : ℝ) * (p / 2) ^ 3 *
          (Real.sqrt (2 / p) * Real.sqrt (p / 2)) := by ring
    _ = (2 / 7 : ℝ) * (p / 2) ^ 3 := by rw [hs]; ring
    _ = p ^ 3 / 28 := by ring

theorem gap4 (p : ℝ) (hp : 0 < p) :
    mass p = p ^ 3 / 28 := by
  calc
    mass p =
        ∫ x in (0 : ℝ)..p / 2,
          ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ) := gap1 p hp
    _ = Real.sqrt (2 / p) *
          ∫ x in (0 : ℝ)..p / 2, Real.rpow x ((5 : ℝ) / 2) := gap2 p hp
    _ = p ^ 3 / 28 := gap3 p hp

theorem gap5 (p : ℝ) (hp : 0 < p) :
    xCentroid p =
      1 / mass p *
        ∫ x in (0 : ℝ)..p / 2,
          x * ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ) := by
  unfold xCentroid
  rw [integral_solid_eq_iterated p hp (fun q : Point3 => q.1) continuous_fst]
  refine congrArg (fun t : ℝ => 1 / mass p * t) ?_
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  simp

theorem gap6 (p : ℝ) (hp : 0 < p) :
    1 / mass p *
        (∫ x in (0 : ℝ)..p / 2,
          x * ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) =
      p ^ 4 / 72 * (28 / p ^ 3) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp2 : 0 ≤ p / 2 := by positivity
  have hinner :
      (∫ x in (0 : ℝ)..p / 2,
          x * ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) =
        Real.sqrt (2 / p) *
          ∫ x in (0 : ℝ)..p / 2, Real.rpow x ((7 : ℝ) / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp2] at hx
    have hx0 : 0 ≤ x := hx.1
    have h2px : 0 ≤ 2 * p * x := by positivity
    have h2p : 0 ≤ 2 / p := by positivity
    have hr : Real.rpow x ((7 : ℝ) / 2) = x ^ 3 * Real.sqrt x := by
      by_cases hzero : x = 0
      · simp [hzero]
      · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hzero)
        calc
          Real.rpow x ((7 : ℝ) / 2) =
              Real.rpow x ((3 : ℝ) + 1 / 2) := by norm_num
          _ = Real.rpow x (3 : ℝ) * Real.rpow x ((1 : ℝ) / 2) := by
            exact Real.rpow_add hxpos _ _
          _ = x ^ 3 * Real.sqrt x := by
            norm_num [Real.rpow_natCast, Real.sqrt_eq_rpow]
    have hsquare :
        (Real.sqrt (2 / p) * Real.sqrt x * p) ^ 2 =
          (Real.sqrt (2 * p * x)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h2p, Real.sq_sqrt hx0,
        Real.sq_sqrt h2px]
      field_simp [hp0]
    have hleft : 0 ≤ Real.sqrt (2 / p) * Real.sqrt x * p := by positivity
    have hright : 0 ≤ Real.sqrt (2 * p * x) := Real.sqrt_nonneg _
    have hs : Real.sqrt (2 / p) * Real.sqrt x * p = Real.sqrt (2 * p * x) := by
      nlinarith [hsquare]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
    rw [hr, ← hs]
    field_simp [hp0] <;> ring
  have hint :
      (∫ x in (0 : ℝ)..p / 2, Real.rpow x ((7 : ℝ) / 2)) =
        (2 / 9 : ℝ) * Real.rpow (p / 2) ((9 : ℝ) / 2) := by
    convert integral_rpow_of_two_le ((9 : ℝ) / 2) (p / 2) (by norm_num) hp2 using 1 <;>
      norm_num
  rw [gap4 p hp, hinner, hint]
  have hp2pos : 0 < p / 2 := by positivity
  have hr :
      Real.rpow (p / 2) ((9 : ℝ) / 2) =
        (p / 2) ^ 4 * Real.sqrt (p / 2) := by
    calc
      Real.rpow (p / 2) ((9 : ℝ) / 2) =
          Real.rpow (p / 2) ((4 : ℝ) + 1 / 2) := by norm_num
      _ = Real.rpow (p / 2) (4 : ℝ) * Real.rpow (p / 2) ((1 : ℝ) / 2) := by
        exact Real.rpow_add hp2pos _ _
      _ = (p / 2) ^ 4 * Real.sqrt (p / 2) := by
        norm_num [Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [hr]
  have hA : 0 ≤ 2 / p := by positivity
  have hB : 0 ≤ p / 2 := hp2
  have hsquare : (Real.sqrt (2 / p) * Real.sqrt (p / 2)) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    field_simp [hp0]
  have hnonneg : 0 ≤ Real.sqrt (2 / p) * Real.sqrt (p / 2) := by positivity
  have hs : Real.sqrt (2 / p) * Real.sqrt (p / 2) = 1 := by
    nlinarith [hsquare]
  have hmoment :
      Real.sqrt (2 / p) *
          ((2 / 9 : ℝ) * ((p / 2) ^ 4 * Real.sqrt (p / 2))) =
        p ^ 4 / 72 := by
    calc
      Real.sqrt (2 / p) *
          ((2 / 9 : ℝ) * ((p / 2) ^ 4 * Real.sqrt (p / 2))) =
          (2 / 9 : ℝ) * (p / 2) ^ 4 *
            (Real.sqrt (2 / p) * Real.sqrt (p / 2)) := by ring
      _ = p ^ 4 / 72 := by rw [hs]; ring
  rw [hmoment]
  field_simp [hp0] <;> ring

theorem gap7 (p : ℝ) (hp : 0 < p) :
    p ^ 4 / 72 * (28 / p ^ 3) = (7 : ℝ) / 18 * p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  field_simp [hp0] <;> norm_num

theorem gap8 (p : ℝ) (hp : 0 < p) :
    xCentroid p = (7 : ℝ) / 18 * p := by
  calc
    xCentroid p =
        1 / mass p *
          ∫ x in (0 : ℝ)..p / 2,
            x * ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
              ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ) := gap5 p hp
    _ = p ^ 4 / 72 * (28 / p ^ 3) := gap6 p hp
    _ = (7 : ℝ) / 18 * p := gap7 p hp

theorem gap9 (p : ℝ) (hp : 0 < p) :
    yCentroid p =
      1 / mass p *
        ∫ x in (0 : ℝ)..p / 2,
          ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            y * ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ) := by
  unfold yCentroid
  have hf : Continuous (fun q : Point3 => q.2.1) :=
    continuous_fst.comp continuous_snd
  rw [integral_solid_eq_iterated p hp (fun q : Point3 => q.2.1) hf]
  refine congrArg (fun t : ℝ => 1 / mass p * t) ?_
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  apply intervalIntegral.integral_congr
  intro y hy
  dsimp only
  rw [← intervalIntegral.integral_const_mul]
  simp

theorem gap10 (p : ℝ) (hp : 0 < p) :
    1 / mass p *
        (∫ x in (0 : ℝ)..p / 2,
          ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            y * ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) =
      0 := by
  have hid (a : ℝ) : (∫ y in -a..a, y) = 0 := by
    have hderiv (x : ℝ) :
        HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) x x := by
      convert ((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ) using 1 <;>
        simp only [id_eq] <;> ring
    calc
      (∫ y in -a..a, y) =
          (1 / 2 : ℝ) * a ^ 2 - (1 / 2 : ℝ) * (-a) ^ 2 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _hx => hderiv x) (continuous_id.intervalIntegrable (-a) a)
      _ = 0 := by ring
  have hzero :
      (∫ x in (0 : ℝ)..p / 2,
        ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
          y * ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) = 0 := by
    calc
      (∫ x in (0 : ℝ)..p / 2,
        ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
          y * ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) =
          ∫ x in (0 : ℝ)..p / 2, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            calc
              (∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
                  y * ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) =
                  (∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x), y) *
                    (∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ)) := by
                      rw [intervalIntegral.integral_mul_const]
              _ = 0 := by rw [hid]; simp
      _ = 0 := by simp
  rw [hzero]
  simp

theorem gap11 (p : ℝ) (hp : 0 < p) :
    yCentroid p = 0 := by
  calc
    yCentroid p =
        1 / mass p *
          ∫ x in (0 : ℝ)..p / 2,
            ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
              y * ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), (1 : ℝ) := gap9 p hp
    _ = 0 := gap10 p hp

theorem gap12 (p : ℝ) (hp : 0 < p) :
    zCentroid p =
      1 / mass p *
        ∫ x in (0 : ℝ)..p / 2,
          ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), z := by
  unfold zCentroid
  have hf : Continuous (fun q : Point3 => q.2.2) :=
    continuous_snd.comp continuous_snd
  rw [integral_solid_eq_iterated p hp (fun q : Point3 => q.2.2) hf]

theorem gap13 (p : ℝ) (hp : 0 < p) :
    1 / mass p *
        (∫ x in (0 : ℝ)..p / 2,
          ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
            ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), z) =
      p ^ 4 / 704 * (28 / p ^ 3) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp2 : 0 ≤ p / 2 := by positivity
  have hz (a : ℝ) : (∫ z in (0 : ℝ)..a, z) = a ^ 2 / 2 := by
    have hderiv (x : ℝ) :
        HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) x x := by
      convert ((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ) using 1 <;>
        simp only [id_eq] <;> ring
    calc
      (∫ z in (0 : ℝ)..a, z) =
          (1 / 2 : ℝ) * a ^ 2 - (1 / 2 : ℝ) * (0 : ℝ) ^ 2 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _hx => hderiv x) (continuous_id.intervalIntegrable (0 : ℝ) a)
      _ = a ^ 2 / 2 := by ring
  have hinner :
      (∫ x in (0 : ℝ)..p / 2,
        ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
          ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), z) =
        (1 / (4 * p)) * Real.sqrt (2 / p) *
          ∫ x in (0 : ℝ)..p / 2, Real.rpow x ((9 : ℝ) / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp2] at hx
    have hx0 : 0 ≤ x := hx.1
    have h2px : 0 ≤ 2 * p * x := by positivity
    have h2p : 0 ≤ 2 / p := by positivity
    have hr : Real.rpow x ((9 : ℝ) / 2) = x ^ 4 * Real.sqrt x := by
      by_cases hzero : x = 0
      · simp [hzero]
      · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hzero)
        calc
          Real.rpow x ((9 : ℝ) / 2) =
              Real.rpow x ((4 : ℝ) + 1 / 2) := by norm_num
          _ = Real.rpow x (4 : ℝ) * Real.rpow x ((1 : ℝ) / 2) := by
            exact Real.rpow_add hxpos _ _
          _ = x ^ 4 * Real.sqrt x := by
            norm_num [Real.rpow_natCast, Real.sqrt_eq_rpow]
    have hsquare :
        (Real.sqrt (2 / p) * Real.sqrt x * p) ^ 2 =
          (Real.sqrt (2 * p * x)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt h2p, Real.sq_sqrt hx0,
        Real.sq_sqrt h2px]
      field_simp [hp0]
    have hleft : 0 ≤ Real.sqrt (2 / p) * Real.sqrt x * p := by positivity
    have hright : 0 ≤ Real.sqrt (2 * p * x) := Real.sqrt_nonneg _
    have hs : Real.sqrt (2 / p) * Real.sqrt x * p = Real.sqrt (2 * p * x) := by
      nlinarith [hsquare]
    change
      (∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
        ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), z) =
      (1 / (4 * p)) * Real.sqrt (2 / p) * Real.rpow x ((9 : ℝ) / 2)
    rw [hz]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    rw [hr, ← hs]
    field_simp [hp0] <;> ring
  have hint :
      (∫ x in (0 : ℝ)..p / 2, Real.rpow x ((9 : ℝ) / 2)) =
        (2 / 11 : ℝ) * Real.rpow (p / 2) ((11 : ℝ) / 2) := by
    convert integral_rpow_of_two_le ((11 : ℝ) / 2) (p / 2) (by norm_num) hp2 using 1 <;>
      norm_num
  have hp2pos : 0 < p / 2 := by positivity
  have hr :
      Real.rpow (p / 2) ((11 : ℝ) / 2) =
        (p / 2) ^ 5 * Real.sqrt (p / 2) := by
    calc
      Real.rpow (p / 2) ((11 : ℝ) / 2) =
          Real.rpow (p / 2) ((5 : ℝ) + 1 / 2) := by norm_num
      _ = Real.rpow (p / 2) (5 : ℝ) * Real.rpow (p / 2) ((1 : ℝ) / 2) := by
        exact Real.rpow_add hp2pos _ _
      _ = (p / 2) ^ 5 * Real.sqrt (p / 2) := by
        norm_num [Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hA : 0 ≤ 2 / p := by positivity
  have hB : 0 ≤ p / 2 := hp2
  have hsquare : (Real.sqrt (2 / p) * Real.sqrt (p / 2)) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    field_simp [hp0]
  have hnonneg : 0 ≤ Real.sqrt (2 / p) * Real.sqrt (p / 2) := by positivity
  have hs : Real.sqrt (2 / p) * Real.sqrt (p / 2) = 1 := by
    nlinarith [hsquare]
  have hmoment :
      (∫ x in (0 : ℝ)..p / 2,
        ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
          ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), z) =
        p ^ 4 / 704 := by
    rw [hinner, hint, hr]
    calc
      (1 / (4 * p)) * Real.sqrt (2 / p) *
          ((2 / 11 : ℝ) * ((p / 2) ^ 5 * Real.sqrt (p / 2))) =
          (1 / (4 * p)) * (2 / 11 : ℝ) * (p / 2) ^ 5 *
            (Real.sqrt (2 / p) * Real.sqrt (p / 2)) := by ring
      _ = p ^ 4 / 704 := by
        rw [hs]
        field_simp [hp0] <;> norm_num
  rw [gap4 p hp, hmoment]
  field_simp [hp0] <;> ring

theorem gap14 (p : ℝ) (hp : 0 < p) :
    p ^ 4 / 704 * (28 / p ^ 3) = (7 : ℝ) / 176 * p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  field_simp [hp0] <;> norm_num

theorem gap15 (p : ℝ) (hp : 0 < p) :
    zCentroid p = (7 : ℝ) / 176 * p := by
  calc
    zCentroid p =
        1 / mass p *
          ∫ x in (0 : ℝ)..p / 2,
            ∫ y in -Real.sqrt (2 * p * x)..Real.sqrt (2 * p * x),
              ∫ z in (0 : ℝ)..x ^ 2 / (2 * p), z := gap12 p hp
    _ = p ^ 4 / 704 * (28 / p ^ 3) := gap13 p hp
    _ = (7 : ℝ) / 176 * p := gap14 p hp

theorem gap16 (p : ℝ) (hp : 0 < p) :
    (xCentroid p, yCentroid p, zCentroid p) =
      ((7 : ℝ) / 18 * p, 0, (7 : ℝ) / 176 * p) := by
  rw [gap8 p hp, gap11 p hp, gap15 p hp]

end

end ProofGap.Exercise4135
