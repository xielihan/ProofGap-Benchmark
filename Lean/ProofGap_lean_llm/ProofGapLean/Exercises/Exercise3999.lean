import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise3999

noncomputable section

open MeasureTheory
open scoped Interval

local instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

def region (a b : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      1 ≤ Real.sqrt (p.1 / a) + Real.sqrt (p.2 / b) ∧
      Real.sqrt (p.1 / a) + Real.sqrt (p.2 / b) ≤ 2 ∧
      a / (4 * b) ≤ p.1 / p.2 ∧ p.1 / p.2 ≤ a / b}

def regionArea (a b : ℝ) : ℝ :=
  ∫ _p in region a b, (1 : ℝ)

def denominator (a b v : ℝ) : ℝ :=
  Real.sqrt (v / a) + 1 / Real.sqrt b

def xCoord (a b u v : ℝ) : ℝ :=
  u ^ 2 * v / denominator a b v ^ 2

def yCoord (a b u v : ℝ) : ℝ :=
  u ^ 2 / denominator a b v ^ 2

def jacobianAbs (a b u v : ℝ) : ℝ :=
  2 * u ^ 3 / denominator a b v ^ 4

private def parameterRectangle (a b : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (a / (4 * b)) (a / b)

private def inverseMap (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (xCoord a b p.1 p.2, yCoord a b p.1 p.2)

private def inverseMapDeriv (a b u v : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  let d := denominator a b v
  let s := Real.sqrt (v / a)
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![2 * u * v / d ^ 2,
        u ^ 2 / d ^ 2 - u ^ 2 * v / (a * s * d ^ 3);
       2 * u / d ^ 2,
        -u ^ 2 / (a * s * d ^ 3)]).toContinuousLinearMap

private theorem hasFDerivAt_inverseMap
    (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) :
    HasFDerivAt (inverseMap a b) (inverseMapDeriv a b u v) (u, v) := by
  have huF :
      HasFDerivAt (fun p : ℝ × ℝ => p.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (u, v) :=
    hasFDerivAt_fst
  have hvF :
      HasFDerivAt (fun p : ℝ × ℝ => p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) :=
    hasFDerivAt_snd
  have hratio :
      HasFDerivAt (fun p : ℝ × ℝ => p.2 / a)
        ((1 / a) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) := by
    convert hvF.const_mul (1 / a) using 1
    funext p
    ring
  have hs :=
    (Real.hasDerivAt_sqrt
      (div_ne_zero hv.ne' ha.ne')).comp_hasFDerivAt
      (u, v) hratio
  have hd := hs.add_const (1 / Real.sqrt b)
  have hdpos :
      0 < Real.sqrt (v / a) + 1 / Real.sqrt b := by
    have hs0 := Real.sqrt_nonneg (v / a)
    have hb0 : 0 < 1 / Real.sqrt b := by positivity
    linarith
  have hdInv :=
    (hasFDerivAt_inv hdpos.ne').comp (u, v) hd
  have hu2 := huF.mul huF
  have hdInv2 := hdInv.mul hdInv
  have hx := (hu2.mul hvF).mul hdInv2
  have hy := hu2.mul hdInv2
  have hall := hx.prodMk hy
  have hsquare :
      Real.sqrt (v / a) ^ 2 = v / a :=
    Real.sq_sqrt (div_pos hv ha).le
  have hbsquare :
      Real.sqrt b ^ 2 = b :=
    Real.sq_sqrt hb.le
  simp only [inverseMap, xCoord, yCoord, inverseMapDeriv, denominator] at ⊢
  convert hall using 1
  · funext p
    unfold inverseMap xCoord yCoord denominator
    rw [show p.2 / a = (1 / a) * p.2 by ring]
    ext <;>
      simp [Function.comp_def, div_eq_mul_inv] <;>
      rw [← inv_pow] <;>
      congr 2 <;>
      ring
  · apply ContinuousLinearMap.ext
    rintro ⟨du, dv⟩
    ext <;>
      simp [Matrix.toLin_finTwoProd_toContinuousLinearMap,
        Function.comp_def] <;>
      field_simp [ha.ne', hdpos.ne',
        Real.sqrt_ne_zero'.mpr (div_pos hv ha)] <;>
      ring

private theorem inverseMapDeriv_det
    (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) :
    (inverseMapDeriv a b u v).det = -jacobianAbs a b u v := by
  have hs : Real.sqrt (v / a) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (div_pos hv ha)
  have hd :
      denominator a b v ≠ 0 := by
    unfold denominator
    have hs0 := Real.sqrt_nonneg (v / a)
    have hb0 : 0 < 1 / Real.sqrt b := by positivity
    linarith
  unfold inverseMapDeriv jacobianAbs
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  field_simp [ha.ne', hs, hd]
  ring

private theorem inverseMap_coordinates
    (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt ((inverseMap a b (u, v)).1 / a) +
          Real.sqrt ((inverseMap a b (u, v)).2 / b) = u ∧
      (inverseMap a b (u, v)).1 / (inverseMap a b (u, v)).2 = v ∧
      0 < (inverseMap a b (u, v)).1 ∧
      0 < (inverseMap a b (u, v)).2 := by
  let d := denominator a b v
  let s := Real.sqrt (v / a)
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (div_pos hv ha)
  have hbroot : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hd : 0 < d := by
    dsimp [d, denominator]
    positivity
  have hssq : s ^ 2 = v / a := by
    dsimp [s]
    exact Real.sq_sqrt (div_pos hv ha).le
  have hbsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hva : v = a * s ^ 2 := by
    field_simp [ha.ne'] at hssq
    linarith
  have hy :
      Real.sqrt ((u ^ 2 / d ^ 2) / b) =
        u / (Real.sqrt b * d) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    field_simp [hb.ne', hbroot.ne', hd.ne']
    nlinarith
  have hx :
      Real.sqrt ((u ^ 2 * v / d ^ 2) / a) =
        u * s / d := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    field_simp [ha.ne', hd.ne']
    nlinarith [hva]
  have hsum :
      u * s / d + u / (Real.sqrt b * d) = u := by
    dsimp [d, denominator, s]
    field_simp [hbroot.ne']
  have hratio :
      (u ^ 2 * v / d ^ 2) / (u ^ 2 / d ^ 2) = v := by
    field_simp [hu.ne', hd.ne']
  unfold inverseMap xCoord yCoord
  change
    Real.sqrt ((u ^ 2 * v / denominator a b v ^ 2) / a) +
          Real.sqrt ((u ^ 2 / denominator a b v ^ 2) / b) = u ∧
      (u ^ 2 * v / denominator a b v ^ 2) /
          (u ^ 2 / denominator a b v ^ 2) = v ∧
      0 < u ^ 2 * v / denominator a b v ^ 2 ∧
      0 < u ^ 2 / denominator a b v ^ 2
  change
    Real.sqrt ((u ^ 2 * v / d ^ 2) / a) +
          Real.sqrt ((u ^ 2 / d ^ 2) / b) = u ∧
      (u ^ 2 * v / d ^ 2) / (u ^ 2 / d ^ 2) = v ∧
      0 < u ^ 2 * v / d ^ 2 ∧
      0 < u ^ 2 / d ^ 2
  exact ⟨by rw [hx, hy]; exact hsum, hratio, by positivity, by positivity⟩

private theorem inverseMap_forward
    (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) :
    inverseMap a b
        (Real.sqrt (x / a) + Real.sqrt (y / b), x / y) =
      (x, y) := by
  let sx := Real.sqrt (x / a)
  let sy := Real.sqrt (y / b)
  have hsx : 0 < sx := by
    dsimp [sx]
    exact Real.sqrt_pos.2 (div_pos hx ha)
  have hsy : 0 < sy := by
    dsimp [sy]
    exact Real.sqrt_pos.2 (div_pos hy hb)
  have hbroot : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hxsq : sx ^ 2 = x / a := by
    dsimp [sx]
    exact Real.sq_sqrt (div_pos hx ha).le
  have hysq : sy ^ 2 = y / b := by
    dsimp [sy]
    exact Real.sq_sqrt (div_pos hy hb).le
  have hxval : x = a * sx ^ 2 := by
    field_simp [ha.ne'] at hxsq
    linarith
  have hyval : y = b * sy ^ 2 := by
    field_simp [hb.ne'] at hysq
    linarith
  have hsratio :
      Real.sqrt ((x / y) / a) =
        sx / (Real.sqrt b * sy) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    field_simp [ha.ne', hb.ne', hy.ne', hbroot.ne', hsy.ne']
    rw [hxval, hyval, Real.sq_sqrt hb.le]
    ring
  have hden :
      denominator a b (x / y) =
        (sx + sy) / (Real.sqrt b * sy) := by
    unfold denominator
    rw [hsratio]
    field_simp [hbroot.ne', hsy.ne']
  have hsum : 0 < sx + sy := add_pos hsx hsy
  have hycoord :
      (sx + sy) ^ 2 / denominator a b (x / y) ^ 2 = y := by
    rw [hden, hyval]
    field_simp [hbroot.ne', hsy.ne', hsum.ne']
    nlinarith [Real.sq_sqrt hb.le]
  have hxcoord :
      (sx + sy) ^ 2 * (x / y) /
          denominator a b (x / y) ^ 2 = x := by
    rw [show
      (sx + sy) ^ 2 * (x / y) /
          denominator a b (x / y) ^ 2 =
        (x / y) *
          ((sx + sy) ^ 2 / denominator a b (x / y) ^ 2) by ring,
      hycoord]
    field_simp [hy.ne']
  unfold inverseMap xCoord yCoord
  change
    ((Real.sqrt (x / a) + Real.sqrt (y / b)) ^ 2 * (x / y) /
        denominator a b (x / y) ^ 2,
      (Real.sqrt (x / a) + Real.sqrt (y / b)) ^ 2 /
        denominator a b (x / y) ^ 2) = (x, y)
  change
    ((sx + sy) ^ 2 * (x / y) / denominator a b (x / y) ^ 2,
      (sx + sy) ^ 2 / denominator a b (x / y) ^ 2) = (x, y)
  exact Prod.ext hxcoord hycoord

private theorem inverseMap_injOn
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Set.InjOn (inverseMap a b) (parameterRectangle a b) := by
  intro p hp q hq hpq
  have hpv : 0 < p.2 := by
    exact lt_of_lt_of_le (by positivity : 0 < a / (4 * b)) hp.2.1
  have hqv : 0 < q.2 := by
    exact lt_of_lt_of_le (by positivity : 0 < a / (4 * b)) hq.2.1
  have hpu : 0 < p.1 := lt_of_lt_of_le zero_lt_one hp.1.1
  have hqu : 0 < q.1 := lt_of_lt_of_le zero_lt_one hq.1.1
  have hpcoords :=
    inverseMap_coordinates a b p.1 p.2 ha hb hpu hpv
  have hqcoords :=
    inverseMap_coordinates a b q.1 q.2 ha hb hqu hqv
  have hu := congrArg
    (fun z : ℝ × ℝ =>
      Real.sqrt (z.1 / a) + Real.sqrt (z.2 / b)) hpq
  have hv := congrArg (fun z : ℝ × ℝ => z.1 / z.2) hpq
  change
    Real.sqrt ((inverseMap a b (p.1, p.2)).1 / a) +
        Real.sqrt ((inverseMap a b (p.1, p.2)).2 / b) =
      Real.sqrt ((inverseMap a b (q.1, q.2)).1 / a) +
        Real.sqrt ((inverseMap a b (q.1, q.2)).2 / b) at hu
  change
    (inverseMap a b (p.1, p.2)).1 /
        (inverseMap a b (p.1, p.2)).2 =
      (inverseMap a b (q.1, q.2)).1 /
        (inverseMap a b (q.1, q.2)).2 at hv
  rw [hpcoords.1, hqcoords.1] at hu
  rw [hpcoords.2.1, hqcoords.2.1] at hv
  exact Prod.ext hu hv

private theorem inverseMap_image
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    inverseMap a b '' parameterRectangle a b = region a b := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hv : 0 < p.2 :=
      lt_of_lt_of_le (by positivity : 0 < a / (4 * b)) hp.2.1
    have hu : 0 < p.1 := lt_of_lt_of_le zero_lt_one hp.1.1
    have hc := inverseMap_coordinates a b p.1 p.2 ha hb hu hv
    change
      0 ≤ (inverseMap a b p).1 ∧
        0 ≤ (inverseMap a b p).2 ∧
        1 ≤ Real.sqrt ((inverseMap a b p).1 / a) +
          Real.sqrt ((inverseMap a b p).2 / b) ∧
        Real.sqrt ((inverseMap a b p).1 / a) +
          Real.sqrt ((inverseMap a b p).2 / b) ≤ 2 ∧
        a / (4 * b) ≤
          (inverseMap a b p).1 / (inverseMap a b p).2 ∧
        (inverseMap a b p).1 / (inverseMap a b p).2 ≤ a / b
    exact
      ⟨hc.2.2.1.le, hc.2.2.2.le,
        by rw [hc.1]; exact hp.1.1,
        by rw [hc.1]; exact hp.1.2,
        by rw [hc.2.1]; exact hp.2.1,
        by rw [hc.2.1]; exact hp.2.2⟩
  · intro hz
    change
      0 ≤ z.1 ∧ 0 ≤ z.2 ∧
        1 ≤ Real.sqrt (z.1 / a) + Real.sqrt (z.2 / b) ∧
        Real.sqrt (z.1 / a) + Real.sqrt (z.2 / b) ≤ 2 ∧
        a / (4 * b) ≤ z.1 / z.2 ∧ z.1 / z.2 ≤ a / b at hz
    have hratio : 0 < z.1 / z.2 :=
      lt_of_lt_of_le (by positivity : 0 < a / (4 * b)) hz.2.2.2.2.1
    have hxy := (div_pos_iff.mp hratio)
    have hx : 0 < z.1 := by
      rcases hxy with hxy | hxy
      · exact hxy.1
      · linarith
    have hy : 0 < z.2 := by
      rcases (div_pos_iff.mp hratio) with hxy | hxy
      · exact hxy.2
      · linarith
    let p : ℝ × ℝ :=
      (Real.sqrt (z.1 / a) + Real.sqrt (z.2 / b), z.1 / z.2)
    refine ⟨p, ?_, ?_⟩
    · exact
        ⟨⟨hz.2.2.1, hz.2.2.2.1⟩,
          ⟨hz.2.2.2.2.1, hz.2.2.2.2.2⟩⟩
    · dsimp [p]
      exact inverseMap_forward a b z.1 z.2 ha hb hx hy

private theorem parameterRectangle_measurable (a b : ℝ) :
    MeasurableSet (parameterRectangle a b) := by
  exact measurableSet_Icc.prod measurableSet_Icc

private theorem setIntegral_Icc_eq_interval
    {c d : ℝ} (hcd : c ≤ d) (f : ℝ → ℝ) :
    (∫ x in Set.Icc c d, f x) = ∫ x in c..d, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hcd]

private theorem parameterRectangle_integral
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ p in parameterRectangle a b, jacobianAbs a b p.1 p.2) =
      ∫ u in (1 : ℝ)..2,
        ∫ v in a / (4 * b)..a / b, jacobianAbs a b u v := by
  have hvbounds : a / (4 * b) ≤ a / b := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * b) hb).2
    nlinarith
  have hden (v : ℝ) : denominator a b v ≠ 0 := by
    unfold denominator
    have hs := Real.sqrt_nonneg (v / a)
    have hc : 0 < 1 / Real.sqrt b := by positivity
    linarith
  have hjcont :
      Continuous (fun p : ℝ × ℝ => jacobianAbs a b p.1 p.2) := by
    unfold jacobianAbs denominator
    exact
      (continuous_const.mul (continuous_fst.pow 3)).div
        ((((Real.continuous_sqrt.comp
          (continuous_snd.div_const a)).add continuous_const).pow 4))
        (fun p => pow_ne_zero 4 (hden p.2))
  have hint :
      IntegrableOn (fun p : ℝ × ℝ => jacobianAbs a b p.1 p.2)
        (parameterRectangle a b) := by
    exact hjcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  unfold parameterRectangle
  rw [Measure.volume_eq_prod]
  have hfubini :=
    MeasureTheory.setIntegral_prod
      (μ := volume) (ν := volume)
      (fun p : ℝ × ℝ => jacobianAbs a b p.1 p.2) hint
  rw [hfubini]
  rw [setIntegral_Icc_eq_interval (by norm_num : (1 : ℝ) ≤ 2)]
  apply intervalIntegral.integral_congr
  intro u _
  simpa using
    (setIntegral_Icc_eq_interval hvbounds
      (fun v => jacobianAbs a b u v))

theorem gap1 (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    xCoord a b u v =
      u ^ 2 * v /
        (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 2 := by
  rfl

theorem gap2 (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    yCoord a b u v =
      u ^ 2 /
        (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 2 := by
  rfl

theorem gap3 (a b x y u v : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : (x, y) ∈ region a b)
    (hu : u = Real.sqrt (x / a) + Real.sqrt (y / b))
    (hv : v = x / y) :
    1 ≤ u := by
  change
    0 ≤ x ∧ 0 ≤ y ∧
      1 ≤ Real.sqrt (x / a) + Real.sqrt (y / b) ∧
      Real.sqrt (x / a) + Real.sqrt (y / b) ≤ 2 ∧
      a / (4 * b) ≤ x / y ∧ x / y ≤ a / b at hp
  rw [hu]
  exact hp.2.2.1

theorem gap4 (a b x y u v : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : (x, y) ∈ region a b)
    (hu : u = Real.sqrt (x / a) + Real.sqrt (y / b))
    (hv : v = x / y) :
    u ≤ 2 := by
  change
    0 ≤ x ∧ 0 ≤ y ∧
      1 ≤ Real.sqrt (x / a) + Real.sqrt (y / b) ∧
      Real.sqrt (x / a) + Real.sqrt (y / b) ≤ 2 ∧
      a / (4 * b) ≤ x / y ∧ x / y ≤ a / b at hp
  rw [hu]
  exact hp.2.2.2.1

theorem gap5 (a b x y u v : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : (x, y) ∈ region a b)
    (hu : u = Real.sqrt (x / a) + Real.sqrt (y / b))
    (hv : v = x / y) :
    a / (4 * b) ≤ v := by
  change
    0 ≤ x ∧ 0 ≤ y ∧
      1 ≤ Real.sqrt (x / a) + Real.sqrt (y / b) ∧
      Real.sqrt (x / a) + Real.sqrt (y / b) ≤ 2 ∧
      a / (4 * b) ≤ x / y ∧ x / y ≤ a / b at hp
  rw [hv]
  exact hp.2.2.2.2.1

theorem gap6 (a b x y u v : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : (x, y) ∈ region a b)
    (hu : u = Real.sqrt (x / a) + Real.sqrt (y / b))
    (hv : v = x / y) :
    v ≤ a / b := by
  change
    0 ≤ x ∧ 0 ≤ y ∧
      1 ≤ Real.sqrt (x / a) + Real.sqrt (y / b) ∧
      Real.sqrt (x / a) + Real.sqrt (y / b) ≤ 2 ∧
      a / (4 * b) ≤ x / y ∧ x / y ≤ a / b at hp
  rw [hv]
  exact hp.2.2.2.2.2

theorem gap7 (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 1 ≤ u) (hv : a / (4 * b) ≤ v) :
    jacobianAbs a b u v =
      2 * u ^ 3 /
        (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 4 := by
  rfl

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    15 / 2 *
        (∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
          2 * a * t / (t + 1 / Real.sqrt b) ^ 4) =
      15 * a *
        ∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
          1 / (t + 1 / Real.sqrt b) ^ 3 -
            (1 / Real.sqrt b) /
              (t + 1 / Real.sqrt b) ^ 4 := by
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases h : t + 1 / Real.sqrt b = 0
  · have h' : t + (Real.sqrt b)⁻¹ = 0 := by
      simpa [one_div] using h
    simp [h']
  · field_simp [h]
    ring

theorem gap11 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    15 * a *
        (∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
          1 / (t + 1 / Real.sqrt b) ^ 3 -
            (1 / Real.sqrt b) /
              (t + 1 / Real.sqrt b) ^ 4) =
      65 * a * b / 108 := by
  let c : ℝ := 1 / Real.sqrt b
  let F : ℝ → ℝ := fun t =>
    -1 / (2 * (t + c) ^ 2) + c / (3 * (t + c) ^ 3)
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hlower : 1 / (2 * Real.sqrt b) = c / 2 := by
    dsimp [c]
    field_simp [ne_of_gt hs]
  have hbounds : 1 / (2 * Real.sqrt b) ≤ 1 / Real.sqrt b := by
    rw [hlower]
    dsimp [c] at hc ⊢
    linarith
  have hF (t : ℝ) (ht : 0 < t + c) :
      HasDerivAt F (1 / (t + c) ^ 3 - c / (t + c) ^ 4) t := by
    have hz : HasDerivAt (fun z : ℝ => z + c) 1 t :=
      (hasDerivAt_id t).add_const c
    have h2 : 2 * (t + c) ^ 2 ≠ 0 := by positivity
    have h3 : 3 * (t + c) ^ 3 ≠ 0 := by positivity
    dsimp [F]
    convert
      ((hasDerivAt_const t (-1)).div
          ((hasDerivAt_const t 2).mul (hz.pow 2)) h2).add
        ((hasDerivAt_const t c).div
          ((hasDerivAt_const t 3).mul (hz.pow 3)) h3) using 1 <;>
      simp only [Pi.mul_apply, Pi.pow_apply] <;>
      field_simp [ne_of_gt ht] <;>
      ring
  have hpos (t : ℝ)
      (ht : t ∈ Set.uIcc (1 / (2 * Real.sqrt b)) (1 / Real.sqrt b)) :
      0 < t + c := by
    rw [Set.uIcc_of_le hbounds] at ht
    rw [hlower] at ht
    change t ∈ Set.Icc (c / 2) c at ht
    rcases ht with ⟨ht, _⟩
    nlinarith
  have hint :
      (∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
          1 / (t + c) ^ 3 - c / (t + c) ^ 4) =
        F (1 / Real.sqrt b) - F (1 / (2 * Real.sqrt b)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      exact hF t (hpos t ht)
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      have hne : t + c ≠ 0 := ne_of_gt (hpos t ht)
      apply ContinuousAt.continuousWithinAt
      exact
        (continuousAt_const.div
            ((continuousAt_id.add continuousAt_const).pow 3)
            (pow_ne_zero 3 hne)).sub
          (continuousAt_const.div
            ((continuousAt_id.add continuousAt_const).pow 4)
            (pow_ne_zero 4 hne))
  change
    15 * a *
        (∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
          1 / (t + c) ^ 3 - c / (t + c) ^ 4) =
      65 * a * b / 108
  rw [hint]
  dsimp [F, c]
  field_simp [ne_of_gt hs]
  nlinarith [Real.sq_sqrt hb.le]

private theorem doubleIntegral_reduction
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u in (1 : ℝ)..2,
        ∫ v in a / (4 * b)..a / b,
          2 * u ^ 3 /
            (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 4) =
      15 / 2 *
        ∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
          2 * a * t / (t + 1 / Real.sqrt b) ^ 4 := by
  let q : ℝ → ℝ := fun v =>
    1 / (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 4
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hc : 0 < 1 / Real.sqrt b := by positivity
  have hden (v : ℝ) :
      Real.sqrt (v / a) + 1 / Real.sqrt b ≠ 0 := by
    have hv := Real.sqrt_nonneg (v / a)
    positivity
  have hq : Continuous q := by
    dsimp [q]
    exact
      continuous_const.div
        (((Real.continuous_sqrt.comp
          (continuous_id.div_const a)).add continuous_const).pow 4)
        (fun v => pow_ne_zero 4 (hden v))
  have hinner (u : ℝ) :
      (∫ v in a / (4 * b)..a / b,
          2 * u ^ 3 /
            (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 4) =
        2 * u ^ 3 * ∫ v in a / (4 * b)..a / b, q v := by
    calc
      _ = ∫ v in a / (4 * b)..a / b, (2 * u ^ 3) * q v := by
        apply intervalIntegral.integral_congr
        intro v _
        dsimp [q]
        ring
      _ = 2 * u ^ 3 * ∫ v in a / (4 * b)..a / b, q v :=
        by
          simpa only using
            (intervalIntegral.integral_const_mul
              (a := a / (4 * b)) (b := a / b) (2 * u ^ 3) q)
  have hu :
      (∫ u in (1 : ℝ)..2, 2 * u ^ 3) = 15 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      integral_pow]
    norm_num
  have hfactor :
      (∫ u in (1 : ℝ)..2,
          ∫ v in a / (4 * b)..a / b,
            2 * u ^ 3 /
              (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 4) =
        15 / 2 * ∫ v in a / (4 * b)..a / b, q v := by
    simp_rw [hinner]
    rw [intervalIntegral.integral_mul_const, hu]
  rw [hfactor]
  congr 1
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv
      (a := 1 / (2 * Real.sqrt b)) (b := 1 / Real.sqrt b)
      (f := fun t : ℝ => a * t ^ 2)
      (f' := fun t : ℝ => 2 * a * t) (g := q)
      (fun t _ => by
        convert (hasDerivAt_const t a).mul ((hasDerivAt_id t).pow 2) using 1 <;>
          simp [id] <;>
          ring)
      ((continuous_const.mul continuous_id).continuousOn) hq
  have hlower :
      a * (1 / (2 * Real.sqrt b)) ^ 2 = a / (4 * b) := by
    field_simp [ne_of_gt hs]
    nlinarith [Real.sq_sqrt hb.le]
  have hupper :
      a * (1 / Real.sqrt b) ^ 2 = a / b := by
    field_simp [ne_of_gt hs, ne_of_gt hb]
    nlinarith [Real.sq_sqrt hb.le]
  change
    (∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
        q (a * t ^ 2) * (2 * a * t)) =
      ∫ v in a * (1 / (2 * Real.sqrt b)) ^ 2..
          a * (1 / Real.sqrt b) ^ 2, q v at hsub
  rw [hlower, hupper] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t ht
  have hbounds :
      1 / (2 * Real.sqrt b) ≤ 1 / Real.sqrt b := by
    have : 1 / (2 * Real.sqrt b) = (1 / Real.sqrt b) / 2 := by
      field_simp [ne_of_gt hs]
    rw [this]
    linarith
  rw [Set.uIcc_of_le hbounds] at ht
  have ht0 : 0 ≤ t := by
    have hl : 0 < 1 / (2 * Real.sqrt b) := by positivity
    rcases ht with ⟨ht, _⟩
    linarith
  have hsqrt :
      Real.sqrt ((a * t ^ 2) / a) = t := by
    rw [mul_div_cancel_left₀ _ (ne_of_gt ha)]
    exact Real.sqrt_sq_eq_abs t |>.trans (abs_of_nonneg ht0)
  dsimp [q]
  rw [hsqrt]
  ring

theorem gap8 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    regionArea a b =
      ∫ u in (1 : ℝ)..2,
        ∫ v in a / (4 * b)..a / b,
          2 * u ^ 3 /
            (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 4 := by
  have hderiv :
      ∀ p ∈ parameterRectangle a b,
        HasFDerivWithinAt (inverseMap a b)
          (inverseMapDeriv a b p.1 p.2) (parameterRectangle a b) p := by
    intro p hp
    have hv : 0 < p.2 :=
      lt_of_lt_of_le (by positivity : 0 < a / (4 * b)) hp.2.1
    exact
      (hasFDerivAt_inverseMap a b p.1 p.2 ha hb hv).hasFDerivWithinAt
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (parameterRectangle_measurable a b) hderiv
      (inverseMap_injOn a b ha hb)
      (fun _p : ℝ × ℝ => (1 : ℝ))
  rw [inverseMap_image a b ha hb] at hchange
  have hrhs :
      (∫ p in parameterRectangle a b,
          |(inverseMapDeriv a b p.1 p.2).det| • (1 : ℝ)) =
        ∫ p in parameterRectangle a b, jacobianAbs a b p.1 p.2 := by
    apply setIntegral_congr_fun (parameterRectangle_measurable a b)
    intro p hp
    have hu : 0 < p.1 := lt_of_lt_of_le zero_lt_one hp.1.1
    have hv : 0 < p.2 :=
      lt_of_lt_of_le (by positivity : 0 < a / (4 * b)) hp.2.1
    have hd : 0 < denominator a b p.2 := by
      unfold denominator
      positivity
    have hj : 0 < jacobianAbs a b p.1 p.2 := by
      unfold jacobianAbs
      positivity
    change |(inverseMapDeriv a b p.1 p.2).det| * 1 =
      jacobianAbs a b p.1 p.2
    rw [inverseMapDeriv_det a b p.1 p.2 ha hb hv, abs_neg,
      abs_of_pos hj, mul_one]
  unfold regionArea
  calc
    (∫ _p in region a b, (1 : ℝ)) =
        ∫ p in parameterRectangle a b,
          |(inverseMapDeriv a b p.1 p.2).det| • (1 : ℝ) := hchange
    _ = ∫ p in parameterRectangle a b, jacobianAbs a b p.1 p.2 := hrhs
    _ = ∫ u in (1 : ℝ)..2,
          ∫ v in a / (4 * b)..a / b, jacobianAbs a b u v :=
      parameterRectangle_integral a b ha hb
    _ = ∫ u in (1 : ℝ)..2,
          ∫ v in a / (4 * b)..a / b,
            2 * u ^ 3 /
              (Real.sqrt (v / a) + 1 / Real.sqrt b) ^ 4 := by
      rfl

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    regionArea a b =
      15 / 2 *
        ∫ t in 1 / (2 * Real.sqrt b)..1 / Real.sqrt b,
          2 * a * t / (t + 1 / Real.sqrt b) ^ 4 := by
  exact (gap8 a b ha hb).trans (doubleIntegral_reduction a b ha hb)

theorem gap12 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    regionArea a b = 65 * a * b / 108 := by
  exact
    (gap9 a b ha hb).trans
      ((gap10 a b ha hb).trans (gap11 a b ha hb))

end

end ProofGap.Exercise3999
