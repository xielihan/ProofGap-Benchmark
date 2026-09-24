import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3998

noncomputable section

open MeasureTheory
open scoped Interval

local instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

def region (p q r s : ℝ) : Set (ℝ × ℝ) :=
  {z |
    2 * p ≤ z.2 ^ 2 / z.1 ∧ z.2 ^ 2 / z.1 ≤ 2 * q ∧
      2 * r ≤ z.1 ^ 2 / z.2 ∧ z.1 ^ 2 / z.2 ≤ 2 * s}

def regionArea (p q r s : ℝ) : ℝ :=
  ∫ _z in region p q r s, (1 : ℝ)

def inverseJacobianDet : ℝ :=
  -1 / 3

private def forwardMap (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2 ^ 2 / z.1, z.1 ^ 2 / z.2)

private def forwardDerivative (x y : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![-y ^ 2 / x ^ 2, 2 * y / x;
       2 * x / y, -x ^ 2 / y ^ 2]).toContinuousLinearMap

private def rectangle (p q r s : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (2 * p) (2 * q) ×ˢ Set.Icc (2 * r) (2 * s)

private def inverseMap (z : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp ((Real.log z.1 + 2 * Real.log z.2) / 3),
    Real.exp ((2 * Real.log z.1 + Real.log z.2) / 3))

private theorem forward_inverse (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    forwardMap (inverseMap (u, v)) = (u, v) := by
  have hxne :
      Real.exp ((Real.log u + 2 * Real.log v) / 3) ≠ 0 :=
    Real.exp_ne_zero _
  have hyne :
      Real.exp ((2 * Real.log u + Real.log v) / 3) ≠ 0 :=
    Real.exp_ne_zero _
  ext
  · change
      Real.exp ((2 * Real.log u + Real.log v) / 3) ^ 2 /
          Real.exp ((Real.log u + 2 * Real.log v) / 3) = u
    rw [div_eq_iff hxne]
    calc
      Real.exp ((2 * Real.log u + Real.log v) / 3) ^ 2 =
          Real.exp
            ((2 * Real.log u + Real.log v) / 3 +
              (2 * Real.log u + Real.log v) / 3) := by
        rw [pow_two, Real.exp_add]
      _ =
          Real.exp
            (Real.log u + (Real.log u + 2 * Real.log v) / 3) := by
        congr 1
        ring
      _ = u * Real.exp ((Real.log u + 2 * Real.log v) / 3) := by
        rw [Real.exp_add, Real.exp_log hu]
  · change
      Real.exp ((Real.log u + 2 * Real.log v) / 3) ^ 2 /
          Real.exp ((2 * Real.log u + Real.log v) / 3) = v
    rw [div_eq_iff hyne]
    calc
      Real.exp ((Real.log u + 2 * Real.log v) / 3) ^ 2 =
          Real.exp
            ((Real.log u + 2 * Real.log v) / 3 +
              (Real.log u + 2 * Real.log v) / 3) := by
        rw [pow_two, Real.exp_add]
      _ =
          Real.exp
            (Real.log v + (2 * Real.log u + Real.log v) / 3) := by
        congr 1
        ring
      _ = v * Real.exp ((2 * Real.log u + Real.log v) / 3) := by
        rw [Real.exp_add, Real.exp_log hv]

private theorem region_measurable (p q r s : ℝ) :
    MeasurableSet (region p q r s) := by
  unfold region
  have hu : Measurable (fun z : ℝ × ℝ => z.2 ^ 2 / z.1) :=
    (measurable_snd.pow_const 2).div measurable_fst
  have hv : Measurable (fun z : ℝ × ℝ => z.1 ^ 2 / z.2) :=
    (measurable_fst.pow_const 2).div measurable_snd
  exact
    (measurableSet_le measurable_const hu).inter
      ((measurableSet_le hu measurable_const).inter
        ((measurableSet_le measurable_const hv).inter
          (measurableSet_le hv measurable_const)))

private theorem region_pos (p q r s : ℝ) (hp : 0 < p) (hr : 0 < r)
    {z : ℝ × ℝ} (hz : z ∈ region p q r s) :
    0 < z.1 ∧ 0 < z.2 := by
  change
    2 * p ≤ z.2 ^ 2 / z.1 ∧ z.2 ^ 2 / z.1 ≤ 2 * q ∧
      2 * r ≤ z.1 ^ 2 / z.2 ∧ z.1 ^ 2 / z.2 ≤ 2 * s at hz
  have hu : 0 < z.2 ^ 2 / z.1 :=
    lt_of_lt_of_le (by positivity) hz.1
  have hv : 0 < z.1 ^ 2 / z.2 :=
    lt_of_lt_of_le (by positivity) hz.2.2.1
  constructor
  · by_contra h
    have hx : z.1 ≤ 0 := le_of_not_gt h
    exact
      (not_lt_of_ge
        (div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hx)) hu
  · by_contra h
    have hy : z.2 ≤ 0 := le_of_not_gt h
    exact
      (not_lt_of_ge
        (div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hy)) hv

private theorem forwardMap_injOn
    (p q r s : ℝ) (hp : 0 < p) (hr : 0 < r) :
    Set.InjOn forwardMap (region p q r s) := by
  intro z hz w hw hzw
  have hzpos := region_pos p q r s hp hr hz
  have hwpos := region_pos p q r s hp hr hw
  have hxne : z.1 ≠ 0 := hzpos.1.ne'
  have hyne : z.2 ≠ 0 := hzpos.2.ne'
  have hXne : w.1 ≠ 0 := hwpos.1.ne'
  have hYne : w.2 ≠ 0 := hwpos.2.ne'
  have h₁ := congrArg Prod.fst hzw
  have h₂ := congrArg Prod.snd hzw
  change z.2 ^ 2 / z.1 = w.2 ^ 2 / w.1 at h₁
  change z.1 ^ 2 / z.2 = w.1 ^ 2 / w.2 at h₂
  have hxcube : z.1 ^ 3 = w.1 ^ 3 := by
    have hprod :
        (z.2 ^ 2 / z.1) * (z.1 ^ 2 / z.2) ^ 2 =
          (w.2 ^ 2 / w.1) * (w.1 ^ 2 / w.2) ^ 2 := by
      rw [h₁, h₂]
    field_simp [hxne, hyne, hXne, hYne] at hprod
    nlinarith
  have hycube : z.2 ^ 3 = w.2 ^ 3 := by
    have hprod :
        (z.2 ^ 2 / z.1) ^ 2 * (z.1 ^ 2 / z.2) =
          (w.2 ^ 2 / w.1) ^ 2 * (w.1 ^ 2 / w.2) := by
      rw [h₁, h₂]
    field_simp [hxne, hyne, hXne, hYne] at hprod
    nlinarith
  ext
  · exact (show Odd 3 by decide).pow_injective hxcube
  · exact (show Odd 3 by decide).pow_injective hycube

private theorem forwardMap_image
    (p q r s : ℝ) (hp : 0 < p) (hr : 0 < r) :
    forwardMap '' region p q r s = rectangle p q r s := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change
      2 * p ≤ w.2 ^ 2 / w.1 ∧ w.2 ^ 2 / w.1 ≤ 2 * q ∧
        2 * r ≤ w.1 ^ 2 / w.2 ∧ w.1 ^ 2 / w.2 ≤ 2 * s at hw
    exact ⟨⟨hw.1, hw.2.1⟩, ⟨hw.2.2.1, hw.2.2.2⟩⟩
  · intro hz
    change
      z.1 ∈ Set.Icc (2 * p) (2 * q) ∧
        z.2 ∈ Set.Icc (2 * r) (2 * s) at hz
    have hu : 0 < z.1 := lt_of_lt_of_le (by positivity) hz.1.1
    have hv : 0 < z.2 := lt_of_lt_of_le (by positivity) hz.2.1
    refine ⟨inverseMap z, ?_, ?_⟩
    · change
        2 * p ≤ (forwardMap (inverseMap z)).1 ∧
          (forwardMap (inverseMap z)).1 ≤ 2 * q ∧
          2 * r ≤ (forwardMap (inverseMap z)).2 ∧
          (forwardMap (inverseMap z)).2 ≤ 2 * s
      rw [show forwardMap (inverseMap z) = z by
        rcases z with ⟨u, v⟩
        exact forward_inverse u v hu hv]
      exact ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2⟩
    · rcases z with ⟨u, v⟩
      exact forward_inverse u v hu hv

private theorem forwardMap_hasFDerivAt
    (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    HasFDerivAt forwardMap (forwardDerivative x y) (x, y) := by
  have hfst :
      HasFDerivAt (fun z : ℝ × ℝ => z.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (x, y) :=
    hasFDerivAt_fst
  have hsnd :
      HasFDerivAt (fun z : ℝ × ℝ => z.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) :=
    hasFDerivAt_snd
  have hfst_inv :=
    (hasFDerivAt_inv hx).comp (x, y) hfst
  have hsnd_inv :=
    (hasFDerivAt_inv hy).comp (x, y) hsnd
  have h₁ := (hsnd.mul hsnd).mul hfst_inv
  have h₂ := (hfst.mul hfst).mul hsnd_inv
  unfold forwardMap forwardDerivative
  convert h₁.prodMk h₂ using 1 <;>
    ext <;>
    simp [Matrix.toLin_finTwoProd_toContinuousLinearMap] <;>
    field_simp [hx, hy] <;>
    ring

private theorem forwardDerivative_det
    (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (forwardDerivative x y).det = -3 := by
  unfold forwardDerivative
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  field_simp [hx, hy]
  ring

private theorem setIntegral_Icc_eq_interval
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

private theorem regionArea_change
    (p q r s : ℝ)
    (hp : 0 < p) (hpq : p < q) (hr : 0 < r) (hrs : r < s) :
    regionArea p q r s =
      1 / 3 *
        ∫ u in 2 * p..2 * q,
          ∫ v in 2 * r..2 * s, (1 : ℝ) := by
  have hderiv :
      ∀ z ∈ region p q r s,
        HasFDerivWithinAt forwardMap (forwardDerivative z.1 z.2)
          (region p q r s) z := by
    intro z hz
    have hzpos := region_pos p q r s hp hr hz
    exact
      (forwardMap_hasFDerivAt z.1 z.2
        hzpos.1.ne' hzpos.2.ne').hasFDerivWithinAt
  have hchange :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (region_measurable p q r s) hderiv
      (forwardMap_injOn p q r s hp hr)
      (fun _z : ℝ × ℝ => (1 : ℝ))
  rw [forwardMap_image p q r s hp hr] at hchange
  have hrect :
      (∫ _z in rectangle p q r s, (1 : ℝ)) =
        ∫ u in 2 * p..2 * q,
          ∫ v in 2 * r..2 * s, (1 : ℝ) := by
    unfold rectangle
    rw [Measure.volume_eq_prod]
    have hprod :
        (∫ _z : ℝ × ℝ in
            Set.Icc (2 * p) (2 * q) ×ˢ Set.Icc (2 * r) (2 * s),
            (1 : ℝ) ∂volume.prod volume) =
          (∫ u in Set.Icc (2 * p) (2 * q), (1 : ℝ)) *
            ∫ v in Set.Icc (2 * r) (2 * s), (1 : ℝ) := by
      simpa only [one_mul] using
        (MeasureTheory.setIntegral_prod_mul
          (μ := volume) (ν := volume)
          (fun _u : ℝ => (1 : ℝ)) (fun _v : ℝ => (1 : ℝ))
          (Set.Icc (2 * p) (2 * q)) (Set.Icc (2 * r) (2 * s)))
    rw [hprod]
    rw [setIntegral_Icc_eq_interval
        (by linarith : 2 * p ≤ 2 * q),
      setIntegral_Icc_eq_interval
        (by linarith : 2 * r ≤ 2 * s)]
    simp
  have hchange' :
      (∫ _z in rectangle p q r s, (1 : ℝ)) =
        ∫ z in region p q r s, (3 : ℝ) := by
    calc
      (∫ _z in rectangle p q r s, (1 : ℝ)) =
          ∫ z in region p q r s,
            |(forwardDerivative z.1 z.2).det| • (1 : ℝ) := hchange
      _ = ∫ z in region p q r s, (3 : ℝ) := by
        apply setIntegral_congr_fun (region_measurable p q r s)
        intro z hz
        have hzpos := region_pos p q r s hp hr hz
        change |(forwardDerivative z.1 z.2).det| * 1 = 3
        rw [forwardDerivative_det z.1 z.2
          hzpos.1.ne' hzpos.2.ne']
        norm_num
  rw [hrect] at hchange'
  rw [show (fun _z : ℝ × ℝ => (3 : ℝ)) =
      fun _z => 3 * (1 : ℝ) by funext; ring,
    MeasureTheory.integral_const_mul] at hchange'
  unfold regionArea
  linarith

theorem gap1 (p q r s x y u v : ℝ)
    (hz : (x, y) ∈ region p q r s)
    (hu : u = y ^ 2 / x) (hv : v = x ^ 2 / y) :
    2 * p ≤ u := by
  change
    2 * p ≤ y ^ 2 / x ∧ y ^ 2 / x ≤ 2 * q ∧
      2 * r ≤ x ^ 2 / y ∧ x ^ 2 / y ≤ 2 * s at hz
  rw [hu]
  exact hz.1

theorem gap2 (p q r s x y u v : ℝ)
    (hz : (x, y) ∈ region p q r s)
    (hu : u = y ^ 2 / x) (hv : v = x ^ 2 / y) :
    u ≤ 2 * q := by
  change
    2 * p ≤ y ^ 2 / x ∧ y ^ 2 / x ≤ 2 * q ∧
      2 * r ≤ x ^ 2 / y ∧ x ^ 2 / y ≤ 2 * s at hz
  rw [hu]
  exact hz.2.1

theorem gap3 (p q r s x y u v : ℝ)
    (hz : (x, y) ∈ region p q r s)
    (hu : u = y ^ 2 / x) (hv : v = x ^ 2 / y) :
    2 * r ≤ v := by
  change
    2 * p ≤ y ^ 2 / x ∧ y ^ 2 / x ≤ 2 * q ∧
      2 * r ≤ x ^ 2 / y ∧ x ^ 2 / y ≤ 2 * s at hz
  rw [hv]
  exact hz.2.2.1

theorem gap4 (p q r s x y u v : ℝ)
    (hz : (x, y) ∈ region p q r s)
    (hu : u = y ^ 2 / x) (hv : v = x ^ 2 / y) :
    v ≤ 2 * s := by
  change
    2 * p ≤ y ^ 2 / x ∧ y ^ 2 / x ≤ 2 * q ∧
      2 * r ≤ x ^ 2 / y ∧ x ^ 2 / y ≤ 2 * s at hz
  rw [hv]
  exact hz.2.2.2

theorem gap5 :
    |inverseJacobianDet| = 1 / 3 := by
  norm_num [inverseJacobianDet]

theorem gap6 (p q r s : ℝ)
    (hp : 0 < p) (hpq : p < q) (hr : 0 < r) (hrs : r < s) :
    regionArea p q r s =
      1 / 3 *
        ∫ u in 2 * p..2 * q,
          ∫ v in 2 * r..2 * s, (1 : ℝ) := by
  exact regionArea_change p q r s hp hpq hr hrs

theorem gap7 (p q r s : ℝ) :
    1 / 3 *
        (∫ u in 2 * p..2 * q,
          ∫ v in 2 * r..2 * s, (1 : ℝ)) =
      4 / 3 * (q - p) * (s - r) := by
  simp
  ring

theorem gap8 (p q r s : ℝ)
    (hp : 0 < p) (hpq : p < q) (hr : 0 < r) (hrs : r < s) :
    regionArea p q r s =
      4 / 3 * (q - p) * (s - r) := by
  rw [gap6 p q r s hp hpq hr hrs, gap7]

end

end ProofGap.Exercise3998
