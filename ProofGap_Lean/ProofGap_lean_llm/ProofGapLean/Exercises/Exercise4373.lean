import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace ProofGap.Exercise4373

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def normalCosines : Vec3 :=
  (1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3)

def projectedRegion (a : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ a ∧ 0 ≤ p.2 ∧ p.2 ≤ a ∧
    a / 2 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 3 * a / 2}

def projectedArea (a : ℝ) : ℝ :=
  ∫ _p in projectedRegion a, (1 : ℝ)

def planePoint (a : ℝ) (p : ℝ × ℝ) : Vec3 :=
  (p.1, p.2, 3 * a / 2 - p.1 - p.2)

def projectedBoundary (a t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 then
    (a / 2 + a / 2 * t, 0)
  else if t ≤ 2 then
    (a, a / 2 * (t - 1))
  else if t ≤ 3 then
    (a - a / 2 * (t - 2), a / 2 + a / 2 * (t - 2))
  else if t ≤ 4 then
    (a / 2 - a / 2 * (t - 3), a)
  else if t ≤ 5 then
    (0, a - a / 2 * (t - 4))
  else
    (a / 2 * (t - 5), a / 2 - a / 2 * (t - 5))

def boundaryCurve (a t : ℝ) : Vec3 :=
  planePoint a (projectedBoundary a t)

def vectorField (p : Vec3) : Vec3 :=
  (p.2.1 ^ 2 - p.2.2 ^ 2,
    p.2.2 ^ 2 - p.1 ^ 2,
    p.1 ^ 2 - p.2.1 ^ 2)

def curlDotNormal (p : Vec3) : ℝ :=
  (-2 * p.2.1 - 2 * p.2.2) / Real.sqrt 3 +
    (-2 * p.2.2 - 2 * p.1) / Real.sqrt 3 +
    (-2 * p.1 - 2 * p.2.1) / Real.sqrt 3

def stokesSurfaceFlux (a : ℝ) : ℝ :=
  ∫ p in projectedRegion a,
    Real.sqrt 3 * curlDotNormal (planePoint a p)

def lineIntegral (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..6,
    (vectorField (boundaryCurve a t)).1 *
        deriv (fun s => (boundaryCurve a s).1) t +
      (vectorField (boundaryCurve a t)).2.1 *
        deriv (fun s => (boundaryCurve a s).2.1) t +
      (vectorField (boundaryCurve a t)).2.2 *
        deriv (fun s => (boundaryCurve a s).2.2) t

theorem gap1 :
    (normalCosines).1 = 1 / Real.sqrt 3 := by
  rfl

theorem gap2 :
    (normalCosines).2.1 = 1 / Real.sqrt 3 := by
  rfl

theorem gap3 :
    (normalCosines).2.2 = 1 / Real.sqrt 3 := by
  rfl

private theorem sqrt_three_ne : Real.sqrt 3 ≠ 0 := by
  positivity

private theorem surface_integrand_formula (a : ℝ) (p : ℝ × ℝ) :
    Real.sqrt 3 * curlDotNormal (planePoint a p) = -6 * a := by
  unfold curlDotNormal planePoint
  dsimp
  field_simp [sqrt_three_ne]
  ring

private theorem stokesSurfaceFlux_eq_area (a : ℝ) :
    stokesSurfaceFlux a = -6 * a * projectedArea a := by
  unfold stokesSurfaceFlux projectedArea
  calc
    (∫ p in projectedRegion a,
        Real.sqrt 3 * curlDotNormal (planePoint a p)) =
        ∫ _p in projectedRegion a, -6 * a := by
      apply MeasureTheory.setIntegral_congr_fun
        (by
          unfold projectedRegion
          measurability)
      intro p hp
      exact surface_integrand_formula a p
    _ = -6 * a * ∫ _p in projectedRegion a, (1 : ℝ) := by
      rw [← MeasureTheory.integral_const_mul]
      simp

private def sliceLower (a x : ℝ) : ℝ :=
  max 0 (a / 2 - x)

private def sliceUpper (a x : ℝ) : ℝ :=
  min a (3 * a / 2 - x)

private theorem slice_bounds_left
    (a x : ℝ) (hx : x ≤ a / 2) :
    sliceLower a x = a / 2 - x ∧ sliceUpper a x = a := by
  constructor
  · unfold sliceLower
    rw [max_eq_right]
    linarith
  · unfold sliceUpper
    rw [min_eq_left]
    linarith

private theorem slice_bounds_right
    (a x : ℝ) (hx : a / 2 ≤ x) :
    sliceLower a x = 0 ∧ sliceUpper a x = 3 * a / 2 - x := by
  constructor
  · unfold sliceLower
    rw [max_eq_left]
    linarith
  · unfold sliceUpper
    rw [min_eq_right]
    linarith

private theorem mem_projectedRegion_slice_iff
    (a x y : ℝ) (ha : 0 < a) (hx : x ∈ Set.Icc (0 : ℝ) a) :
    (x, y) ∈ projectedRegion a ↔
      y ∈ Set.Icc (sliceLower a x) (sliceUpper a x) := by
  by_cases hm : x ≤ a / 2
  · obtain ⟨hlo, hhi⟩ := slice_bounds_left a x hm
    rw [hlo, hhi]
    unfold projectedRegion
    simp only [Set.mem_setOf_eq, Prod.fst, Prod.snd, Set.mem_Icc]
    constructor
    · intro h
      exact ⟨by linarith [h.2.2.2.2.1], h.2.2.2.1⟩
    · intro h
      exact ⟨hx.1, hx.2, by linarith, h.2, by linarith, by linarith⟩
  · have hm' : a / 2 ≤ x := le_of_lt (lt_of_not_ge hm)
    obtain ⟨hlo, hhi⟩ := slice_bounds_right a x hm'
    rw [hlo, hhi]
    unfold projectedRegion
    simp only [Set.mem_setOf_eq, Prod.fst, Prod.snd, Set.mem_Icc]
    constructor
    · intro h
      exact ⟨h.2.2.1, by linarith [h.2.2.2.2.2]⟩
    · intro h
      exact ⟨hx.1, hx.2, h.1, by linarith, by linarith, by linarith⟩

private theorem sliceLower_le_sliceUpper
    (a x : ℝ) (ha : 0 < a) (hx : x ∈ Set.Icc (0 : ℝ) a) :
    sliceLower a x ≤ sliceUpper a x := by
  by_cases hm : x ≤ a / 2
  · obtain ⟨hlo, hhi⟩ := slice_bounds_left a x hm
    rw [hlo, hhi]
    linarith [hx.1]
  · have hm' : a / 2 ≤ x := le_of_lt (lt_of_not_ge hm)
    obtain ⟨hlo, hhi⟩ := slice_bounds_right a x hm'
    rw [hlo, hhi]
    linarith [hx.2]

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

private theorem integral_indicator_Icc_eq_interval
    (u v : ℝ) (f : ℝ → ℝ) (huv : u ≤ v) :
    (∫ x : ℝ, (Set.Icc u v).indicator f x) =
      ∫ x in u..v, f x := by
  rw [intervalIntegral.integral_of_le huv]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_real_ne u] with x hx
  by_cases hxc : x ∈ Set.Icc u v
  · have hxo : x ∈ Set.Ioc u v :=
      ⟨lt_of_le_of_ne hxc.1 (Ne.symm hx), hxc.2⟩
    simp [hxc, hxo]
  · have hxo : x ∉ Set.Ioc u v := fun h => hxc ⟨h.1.le, h.2⟩
    simp [hxc, hxo]

private theorem projectedArea_formula (a : ℝ) (ha : 0 < a) :
    projectedArea a = 3 / 4 * a ^ 2 := by
  classical
  let one : ℝ × ℝ → ℝ := fun _p => 1
  have hregion : MeasurableSet (projectedRegion a) := by
    unfold projectedRegion
    measurability
  have hsubset :
      projectedRegion a ⊆ Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a := by
    intro p hp
    exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2.1⟩⟩
  have honeRect :
      IntegrableOn one (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) a) := by
    exact continuous_const.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have honeRegion : IntegrableOn one (projectedRegion a) :=
    honeRect.mono_set hsubset
  have hind : Integrable ((projectedRegion a).indicator one) :=
    (integrable_indicator_iff hregion).2 honeRegion
  have hprod :
      (∫ p : ℝ × ℝ, (projectedRegion a).indicator one p) =
        ∫ x : ℝ, ∫ y : ℝ,
          (projectedRegion a).indicator one (x, y) := by
    change
      (∫ p : ℝ × ℝ, (projectedRegion a).indicator one p
        ∂(volume.prod volume)) =
        ∫ x : ℝ, ∫ y : ℝ,
          (projectedRegion a).indicator one (x, y)
    exact MeasureTheory.integral_prod
      ((projectedRegion a).indicator one) hind
  have hslice (x : ℝ) :
      (∫ y : ℝ, (projectedRegion a).indicator one (x, y)) =
        (Set.Icc (0 : ℝ) a).indicator
          (fun x =>
            sliceUpper a x - sliceLower a x) x := by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) a
    · rw [Set.indicator_of_mem hx]
      have hbounds := sliceLower_le_sliceUpper a x ha hx
      calc
        (∫ y : ℝ, (projectedRegion a).indicator one (x, y)) =
            ∫ y : ℝ,
              (Set.Icc (sliceLower a x) (sliceUpper a x)).indicator
                (fun _y => (1 : ℝ)) y := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [Set.indicator_apply, Set.indicator_apply]
          rw [mem_projectedRegion_slice_iff a x y ha hx]
          simp [one]
        _ = ∫ _y in sliceLower a x..sliceUpper a x, (1 : ℝ) :=
          integral_indicator_Icc_eq_interval
            (sliceLower a x) (sliceUpper a x) (fun _y => (1 : ℝ)) hbounds
        _ = sliceUpper a x - sliceLower a x := by
          rw [intervalIntegral.integral_const]
          simp
    · rw [Set.indicator_of_notMem hx]
      have hnone (y : ℝ) : (x, y) ∉ projectedRegion a := by
        intro hxy
        exact hx ⟨hxy.1, hxy.2.1⟩
      apply MeasureTheory.integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall (fun y => by
        simp [hnone y])
  have houter :
      (∫ x : ℝ,
          (Set.Icc (0 : ℝ) a).indicator
            (fun x => sliceUpper a x - sliceLower a x) x) =
        ∫ x in (0 : ℝ)..a,
          sliceUpper a x - sliceLower a x :=
    integral_indicator_Icc_eq_interval 0 a
      (fun x => sliceUpper a x - sliceLower a x) ha.le
  have hloCont : Continuous (sliceLower a) := by
    unfold sliceLower
    fun_prop
  have hhiCont : Continuous (sliceUpper a) := by
    unfold sliceUpper
    fun_prop
  have hdiffInt :
      IntervalIntegrable
        (fun x : ℝ => sliceUpper a x - sliceLower a x)
        volume 0 a :=
    (hhiCont.sub hloCont).intervalIntegrable _ _
  have hleft :
      IntervalIntegrable
        (fun x : ℝ => sliceUpper a x - sliceLower a x)
        volume 0 (a / 2) :=
    (hhiCont.sub hloCont).intervalIntegrable _ _
  have hright :
      IntervalIntegrable
        (fun x : ℝ => sliceUpper a x - sliceLower a x)
        volume (a / 2) a :=
    (hhiCont.sub hloCont).intervalIntegrable _ _
  have hleftEval :
      (∫ x in (0 : ℝ)..a / 2,
          sliceUpper a x - sliceLower a x) =
        3 * a ^ 2 / 8 := by
    calc
      _ = ∫ x in (0 : ℝ)..a / 2, a / 2 + x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ a / 2)] at hx
        obtain ⟨hlo, hhi⟩ := slice_bounds_left a x hx.2
        change sliceUpper a x - sliceLower a x = a / 2 + x
        rw [hlo, hhi]
        ring
      _ = 3 * a ^ 2 / 8 := by
        let F : ℝ → ℝ := fun x => a / 2 * x + x ^ 2 / 2
        have hF (x : ℝ) : HasDerivAt F (a / 2 + x) x := by
          dsimp [F]
          convert
            ((hasDerivAt_id x).const_mul (a / 2)).add
              (((hasDerivAt_id x).pow 2).div_const 2)
            using 1 <;> simp only [id_eq] <;> ring
        have hint :
            IntervalIntegrable (fun x : ℝ => a / 2 + x)
              volume 0 (a / 2) := by
          simpa only [id_eq] using
            (continuous_const.add continuous_id).intervalIntegrable
              (0 : ℝ) (a / 2)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hF x) hint]
        dsimp [F]
        ring
  have hrightEval :
      (∫ x in a / 2..a,
          sliceUpper a x - sliceLower a x) =
        3 * a ^ 2 / 8 := by
    calc
      _ = ∫ x in a / 2..a, 3 * a / 2 - x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by linarith : a / 2 ≤ a)] at hx
        obtain ⟨hlo, hhi⟩ := slice_bounds_right a x hx.1
        change sliceUpper a x - sliceLower a x = 3 * a / 2 - x
        rw [hlo, hhi]
        ring
      _ = 3 * a ^ 2 / 8 := by
        let F : ℝ → ℝ := fun x => 3 * a / 2 * x - x ^ 2 / 2
        have hF (x : ℝ) : HasDerivAt F (3 * a / 2 - x) x := by
          dsimp [F]
          convert
            ((hasDerivAt_id x).const_mul (3 * a / 2)).sub
              (((hasDerivAt_id x).pow 2).div_const 2)
            using 1 <;> simp only [id_eq] <;> ring
        have hint :
            IntervalIntegrable (fun x : ℝ => 3 * a / 2 - x)
              volume (a / 2) a := by
          simpa only [id_eq] using
            (continuous_const.sub continuous_id).intervalIntegrable
              (a / 2) a
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx => hF x) hint]
        dsimp [F]
        ring
  unfold projectedArea
  change (∫ p in projectedRegion a, one p) = _
  rw [← MeasureTheory.integral_indicator hregion, hprod]
  simp_rw [hslice]
  rw [houter,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hleftEval, hrightEval]
  ring

private def curveIntegrand (γ : ℝ → Vec3) (t : ℝ) : ℝ :=
  (vectorField (γ t)).1 * deriv (fun s => (γ s).1) t +
    (vectorField (γ t)).2.1 * deriv (fun s => (γ s).2.1) t +
    (vectorField (γ t)).2.2 * deriv (fun s => (γ s).2.2) t

private def segment1 (a t : ℝ) : Vec3 :=
  planePoint a (a / 2 + a / 2 * t, 0)

private def segment2 (a t : ℝ) : Vec3 :=
  planePoint a (a, a / 2 * (t - 1))

private def segment3 (a t : ℝ) : Vec3 :=
  planePoint a
    (a - a / 2 * (t - 2), a / 2 + a / 2 * (t - 2))

private def segment4 (a t : ℝ) : Vec3 :=
  planePoint a (a / 2 - a / 2 * (t - 3), a)

private def segment5 (a t : ℝ) : Vec3 :=
  planePoint a (0, a - a / 2 * (t - 4))

private def segment6 (a t : ℝ) : Vec3 :=
  planePoint a
    (a / 2 * (t - 5), a / 2 - a / 2 * (t - 5))

private theorem curveIntegrand_congr_local
    {γ δ : ℝ → Vec3} {t : ℝ} (h : γ =ᶠ[nhds t] δ) :
    curveIntegrand γ t = curveIntegrand δ t := by
  have hval : γ t = δ t := h.self_of_nhds
  have hx :
      (fun s => (γ s).1) =ᶠ[nhds t] (fun s => (δ s).1) := by
    filter_upwards [h] with s hs
    rw [hs]
  have hy :
      (fun s => (γ s).2.1) =ᶠ[nhds t] (fun s => (δ s).2.1) := by
    filter_upwards [h] with s hs
    rw [hs]
  have hz :
      (fun s => (γ s).2.2) =ᶠ[nhds t] (fun s => (δ s).2.2) := by
    filter_upwards [h] with s hs
    rw [hs]
  unfold curveIntegrand
  rw [hval, hx.deriv_eq, hy.deriv_eq, hz.deriv_eq]

private theorem boundary_eventually_segment1
    (a t : ℝ) (ht : t < 1) :
    boundaryCurve a =ᶠ[nhds t] segment1 a := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  unfold boundaryCurve segment1 projectedBoundary
  rw [if_pos hs.le]

private theorem boundary_eventually_segment2
    (a t : ℝ) (ht1 : 1 < t) (ht2 : t < 2) :
    boundaryCurve a =ᶠ[nhds t] segment2 a := by
  filter_upwards [Ioi_mem_nhds ht1, Iio_mem_nhds ht2] with s hs1 hs2
  unfold boundaryCurve segment2 projectedBoundary
  rw [if_neg (not_le.mpr hs1), if_pos hs2.le]

private theorem boundary_eventually_segment3
    (a t : ℝ) (ht2 : 2 < t) (ht3 : t < 3) :
    boundaryCurve a =ᶠ[nhds t] segment3 a := by
  filter_upwards [Ioi_mem_nhds ht2, Iio_mem_nhds ht3] with s hs2 hs3
  change 2 < s at hs2
  change s < 3 at hs3
  unfold boundaryCurve segment3 projectedBoundary
  rw [if_neg (by linarith), if_neg (not_le.mpr hs2), if_pos hs3.le]

private theorem boundary_eventually_segment4
    (a t : ℝ) (ht3 : 3 < t) (ht4 : t < 4) :
    boundaryCurve a =ᶠ[nhds t] segment4 a := by
  filter_upwards [Ioi_mem_nhds ht3, Iio_mem_nhds ht4] with s hs3 hs4
  change 3 < s at hs3
  change s < 4 at hs4
  unfold boundaryCurve segment4 projectedBoundary
  rw [if_neg (by linarith), if_neg (by linarith),
    if_neg (not_le.mpr hs3), if_pos hs4.le]

private theorem boundary_eventually_segment5
    (a t : ℝ) (ht4 : 4 < t) (ht5 : t < 5) :
    boundaryCurve a =ᶠ[nhds t] segment5 a := by
  filter_upwards [Ioi_mem_nhds ht4, Iio_mem_nhds ht5] with s hs4 hs5
  change 4 < s at hs4
  change s < 5 at hs5
  unfold boundaryCurve segment5 projectedBoundary
  rw [if_neg (by linarith), if_neg (by linarith),
    if_neg (by linarith), if_neg (not_le.mpr hs4), if_pos hs5.le]

private theorem boundary_eventually_segment6
    (a t : ℝ) (ht5 : 5 < t) :
    boundaryCurve a =ᶠ[nhds t] segment6 a := by
  filter_upwards [Ioi_mem_nhds ht5] with s hs5
  change 5 < s at hs5
  unfold boundaryCurve segment6 projectedBoundary
  rw [if_neg (by linarith), if_neg (by linarith),
    if_neg (by linarith), if_neg (by linarith),
    if_neg (not_le.mpr hs5)]

private theorem deriv_affine (m k t : ℝ) :
    deriv (fun s : ℝ => k + m * s) t = m := by
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id t).const_mul m).const_add k).deriv

private theorem deriv_eq_slope
    (f : ℝ → ℝ) (m k t : ℝ)
    (hf : f = fun s : ℝ => k + m * s) :
    deriv f t = m := by
  rw [hf]
  exact deriv_affine m k t

private theorem segment1_formula (a t : ℝ) :
    curveIntegrand (segment1 a) t =
      a ^ 3 * (-5 / 8 + (1 / 4) * t - (1 / 4) * t ^ 2) := by
  have hx :
      deriv (fun s => (segment1 a s).1) t = a / 2 := by
    apply deriv_eq_slope _ (a / 2) (a / 2)
    funext s
    unfold segment1 planePoint
    dsimp
  have hy :
      deriv (fun s => (segment1 a s).2.1) t = 0 := by
    apply deriv_eq_slope _ 0 0
    funext s
    unfold segment1 planePoint
    simp
  have hz :
      deriv (fun s => (segment1 a s).2.2) t = -a / 2 := by
    apply deriv_eq_slope _ (-a / 2) a
    funext s
    unfold segment1 planePoint
    dsimp
    ring
  unfold curveIntegrand
  rw [hx, hy, hz]
  unfold segment1 planePoint vectorField
  dsimp
  ring

private theorem segment2_formula (a t : ℝ) :
    curveIntegrand (segment2 a) t =
      a ^ 3 * (-3 / 8 - (3 / 4) * t + (1 / 4) * t ^ 2) := by
  have hx :
      deriv (fun s => (segment2 a s).1) t = 0 := by
    apply deriv_eq_slope _ 0 a
    funext s
    unfold segment2 planePoint
    simp
  have hy :
      deriv (fun s => (segment2 a s).2.1) t = a / 2 := by
    apply deriv_eq_slope _ (a / 2) (-a / 2)
    funext s
    unfold segment2 planePoint
    dsimp
    ring
  have hz :
      deriv (fun s => (segment2 a s).2.2) t = -a / 2 := by
    apply deriv_eq_slope _ (-a / 2) a
    funext s
    unfold segment2 planePoint
    dsimp
    ring
  unfold curveIntegrand
  rw [hx, hy, hz]
  unfold segment2 planePoint vectorField
  dsimp
  ring

private theorem segment3_formula (a t : ℝ) :
    curveIntegrand (segment3 a) t =
      a ^ 3 * (-17 / 8 + (5 / 4) * t - (1 / 4) * t ^ 2) := by
  have hx :
      deriv (fun s => (segment3 a s).1) t = -a / 2 := by
    apply deriv_eq_slope _ (-a / 2) (2 * a)
    funext s
    unfold segment3 planePoint
    dsimp
    ring
  have hy :
      deriv (fun s => (segment3 a s).2.1) t = a / 2 := by
    apply deriv_eq_slope _ (a / 2) (-a / 2)
    funext s
    unfold segment3 planePoint
    dsimp
    ring
  have hz :
      deriv (fun s => (segment3 a s).2.2) t = 0 := by
    apply deriv_eq_slope _ 0 0
    funext s
    unfold segment3 planePoint
    dsimp
    ring
  unfold curveIntegrand
  rw [hx, hy, hz]
  unfold segment3 planePoint vectorField
  dsimp
  ring

private theorem segment4_formula (a t : ℝ) :
    curveIntegrand (segment4 a) t =
      a ^ 3 * (17 / 8 - (7 / 4) * t + (1 / 4) * t ^ 2) := by
  have hx :
      deriv (fun s => (segment4 a s).1) t = -a / 2 := by
    apply deriv_eq_slope _ (-a / 2) (2 * a)
    funext s
    unfold segment4 planePoint
    dsimp
    ring
  have hy :
      deriv (fun s => (segment4 a s).2.1) t = 0 := by
    apply deriv_eq_slope _ 0 a
    funext s
    unfold segment4 planePoint
    simp
  have hz :
      deriv (fun s => (segment4 a s).2.2) t = a / 2 := by
    apply deriv_eq_slope _ (a / 2) (-3 * a / 2)
    funext s
    unfold segment4 planePoint
    dsimp
    ring
  unfold curveIntegrand
  rw [hx, hy, hz]
  unfold segment4 planePoint vectorField
  dsimp
  ring

private theorem segment5_formula (a t : ℝ) :
    curveIntegrand (segment5 a) t =
      a ^ 3 * (-45 / 8 + (9 / 4) * t - (1 / 4) * t ^ 2) := by
  have hx :
      deriv (fun s => (segment5 a s).1) t = 0 := by
    apply deriv_eq_slope _ 0 0
    funext s
    unfold segment5 planePoint
    simp
  have hy :
      deriv (fun s => (segment5 a s).2.1) t = -a / 2 := by
    apply deriv_eq_slope _ (-a / 2) (3 * a)
    funext s
    unfold segment5 planePoint
    dsimp
    ring
  have hz :
      deriv (fun s => (segment5 a s).2.2) t = a / 2 := by
    apply deriv_eq_slope _ (a / 2) (-3 * a / 2)
    funext s
    unfold segment5 planePoint
    dsimp
    ring
  unfold curveIntegrand
  rw [hx, hy, hz]
  unfold segment5 planePoint vectorField
  dsimp
  ring

private theorem segment6_formula (a t : ℝ) :
    curveIntegrand (segment6 a) t =
      a ^ 3 * (53 / 8 - (11 / 4) * t + (1 / 4) * t ^ 2) := by
  have hx :
      deriv (fun s => (segment6 a s).1) t = a / 2 := by
    apply deriv_eq_slope _ (a / 2) (-5 * a / 2)
    funext s
    unfold segment6 planePoint
    dsimp
    ring
  have hy :
      deriv (fun s => (segment6 a s).2.1) t = -a / 2 := by
    apply deriv_eq_slope _ (-a / 2) (3 * a)
    funext s
    unfold segment6 planePoint
    dsimp
    ring
  have hz :
      deriv (fun s => (segment6 a s).2.2) t = 0 := by
    apply deriv_eq_slope _ 0 a
    funext s
    unfold segment6 planePoint
    simp
    ring
  unfold curveIntegrand
  rw [hx, hy, hz]
  unfold segment6 planePoint vectorField
  dsimp
  ring

private theorem integral_scaled_quadratic
    (A c₀ c₁ c₂ l u : ℝ) :
    (∫ t in l..u, A * (c₀ + c₁ * t + c₂ * t ^ 2)) =
      A * (c₀ * (u - l) +
        c₁ * (u ^ 2 - l ^ 2) / 2 +
        c₂ * (u ^ 3 - l ^ 3) / 3) := by
  let F : ℝ → ℝ :=
    fun t =>
      A * (c₀ * t + c₁ * t ^ 2 / 2 + c₂ * t ^ 3 / 3)
  have hF (t : ℝ) :
      HasDerivAt F (A * (c₀ + c₁ * t + c₂ * t ^ 2)) t := by
    have h1 := hasDerivAt_id t
    have h2 := h1.pow 2
    have h3 := h1.pow 3
    dsimp [F]
    convert
      (((h1.const_mul c₀).add
        ((h2.const_mul c₁).div_const 2)).add
          ((h3.const_mul c₂).div_const 3)).const_mul A
      using 1 <;> simp only [id_eq] <;> ring
  have hint :
      IntervalIntegrable
        (fun t : ℝ => A * (c₀ + c₁ * t + c₂ * t ^ 2))
        volume l u := by
    exact
      (continuous_const.mul
        (continuous_const.add
          (continuous_const.mul continuous_id) |>.add
            (continuous_const.mul (continuous_id.pow 2)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hF t) hint]
  dsimp [F]
  ring

private theorem lineIntegral_formula (a : ℝ) :
    lineIntegral a = -(9 / 2) * a ^ 3 := by
  let f : ℝ → ℝ := curveIntegrand (boundaryCurve a)
  let p1 : ℝ → ℝ :=
    fun t => a ^ 3 * (-5 / 8 + (1 / 4) * t - (1 / 4) * t ^ 2)
  let p2 : ℝ → ℝ :=
    fun t => a ^ 3 * (-3 / 8 - (3 / 4) * t + (1 / 4) * t ^ 2)
  let p3 : ℝ → ℝ :=
    fun t => a ^ 3 * (-17 / 8 + (5 / 4) * t - (1 / 4) * t ^ 2)
  let p4 : ℝ → ℝ :=
    fun t => a ^ 3 * (17 / 8 - (7 / 4) * t + (1 / 4) * t ^ 2)
  let p5 : ℝ → ℝ :=
    fun t => a ^ 3 * (-45 / 8 + (9 / 4) * t - (1 / 4) * t ^ 2)
  let p6 : ℝ → ℝ :=
    fun t => a ^ 3 * (53 / 8 - (11 / 4) * t + (1 / 4) * t ^ 2)
  have heq1 :
      f =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) 1)] p1 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (ae_real_ne (1 : ℝ))] with t ht ht1
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    calc
      f t = curveIntegrand (segment1 a) t := by
        exact curveIntegrand_congr_local
          (boundary_eventually_segment1 a t htlt)
      _ = p1 t := by
        simpa [p1] using segment1_formula a t
  have heq2 :
      f =ᵐ[volume.restrict (Set.uIoc (1 : ℝ) 2)] p2 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (ae_real_ne (2 : ℝ))] with t ht ht2
    rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    have htlt : t < 2 := lt_of_le_of_ne ht.2 ht2
    calc
      f t = curveIntegrand (segment2 a) t := by
        exact curveIntegrand_congr_local
          (boundary_eventually_segment2 a t ht.1 htlt)
      _ = p2 t := by
        simpa [p2] using segment2_formula a t
  have heq3 :
      f =ᵐ[volume.restrict (Set.uIoc (2 : ℝ) 3)] p3 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (ae_real_ne (3 : ℝ))] with t ht ht3
    rw [Set.uIoc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
    have htlt : t < 3 := lt_of_le_of_ne ht.2 ht3
    calc
      f t = curveIntegrand (segment3 a) t := by
        exact curveIntegrand_congr_local
          (boundary_eventually_segment3 a t ht.1 htlt)
      _ = p3 t := by
        simpa [p3] using segment3_formula a t
  have heq4 :
      f =ᵐ[volume.restrict (Set.uIoc (3 : ℝ) 4)] p4 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (ae_real_ne (4 : ℝ))] with t ht ht4
    rw [Set.uIoc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at ht
    have htlt : t < 4 := lt_of_le_of_ne ht.2 ht4
    calc
      f t = curveIntegrand (segment4 a) t := by
        exact curveIntegrand_congr_local
          (boundary_eventually_segment4 a t ht.1 htlt)
      _ = p4 t := by
        simpa [p4] using segment4_formula a t
  have heq5 :
      f =ᵐ[volume.restrict (Set.uIoc (4 : ℝ) 5)] p5 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (ae_real_ne (5 : ℝ))] with t ht ht5
    rw [Set.uIoc_of_le (by norm_num : (4 : ℝ) ≤ 5)] at ht
    have htlt : t < 5 := lt_of_le_of_ne ht.2 ht5
    calc
      f t = curveIntegrand (segment5 a) t := by
        exact curveIntegrand_congr_local
          (boundary_eventually_segment5 a t ht.1 htlt)
      _ = p5 t := by
        simpa [p5] using segment5_formula a t
  have heq6 :
      f =ᵐ[volume.restrict (Set.uIoc (5 : ℝ) 6)] p6 := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le (by norm_num : (5 : ℝ) ≤ 6)] at ht
    calc
      f t = curveIntegrand (segment6 a) t := by
        exact curveIntegrand_congr_local
          (boundary_eventually_segment6 a t ht.1)
      _ = p6 t := by
        simpa [p6] using segment6_formula a t
  have hp1 : IntervalIntegrable p1 volume 0 1 := by
    exact (by
      dsimp [p1]
      fun_prop : Continuous p1).intervalIntegrable _ _
  have hp2 : IntervalIntegrable p2 volume 1 2 := by
    exact (by
      dsimp [p2]
      fun_prop : Continuous p2).intervalIntegrable _ _
  have hp3 : IntervalIntegrable p3 volume 2 3 := by
    exact (by
      dsimp [p3]
      fun_prop : Continuous p3).intervalIntegrable _ _
  have hp4 : IntervalIntegrable p4 volume 3 4 := by
    exact (by
      dsimp [p4]
      fun_prop : Continuous p4).intervalIntegrable _ _
  have hp5 : IntervalIntegrable p5 volume 4 5 := by
    exact (by
      dsimp [p5]
      fun_prop : Continuous p5).intervalIntegrable _ _
  have hp6 : IntervalIntegrable p6 volume 5 6 := by
    exact (by
      dsimp [p6]
      fun_prop : Continuous p6).intervalIntegrable _ _
  have hf1 : IntervalIntegrable f volume 0 1 := hp1.congr_ae heq1.symm
  have hf2 : IntervalIntegrable f volume 1 2 := hp2.congr_ae heq2.symm
  have hf3 : IntervalIntegrable f volume 2 3 := hp3.congr_ae heq3.symm
  have hf4 : IntervalIntegrable f volume 3 4 := hp4.congr_ae heq4.symm
  have hf5 : IntervalIntegrable f volume 4 5 := hp5.congr_ae heq5.symm
  have hf6 : IntervalIntegrable f volume 5 6 := hp6.congr_ae heq6.symm
  have hv1 : (∫ t in (0 : ℝ)..1, f t) = -7 / 12 * a ^ 3 := by
    rw [intervalIntegral.integral_congr_ae_restrict heq1]
    dsimp [p1]
    have h := integral_scaled_quadratic
      (a ^ 3) (-5 / 8) (1 / 4) (-1 / 4) 0 1
    convert h using 1 <;> ring
  have hv2 : (∫ t in (1 : ℝ)..2, f t) = -11 / 12 * a ^ 3 := by
    rw [intervalIntegral.integral_congr_ae_restrict heq2]
    dsimp [p2]
    have h := integral_scaled_quadratic
      (a ^ 3) (-3 / 8) (-3 / 4) (1 / 4) 1 2
    convert h using 1 <;> ring
  have hv3 : (∫ t in (2 : ℝ)..3, f t) = -7 / 12 * a ^ 3 := by
    rw [intervalIntegral.integral_congr_ae_restrict heq3]
    dsimp [p3]
    have h := integral_scaled_quadratic
      (a ^ 3) (-17 / 8) (5 / 4) (-1 / 4) 2 3
    convert h using 1 <;> ring
  have hv4 : (∫ t in (3 : ℝ)..4, f t) = -11 / 12 * a ^ 3 := by
    rw [intervalIntegral.integral_congr_ae_restrict heq4]
    dsimp [p4]
    have h := integral_scaled_quadratic
      (a ^ 3) (17 / 8) (-7 / 4) (1 / 4) 3 4
    convert h using 1 <;> ring
  have hv5 : (∫ t in (4 : ℝ)..5, f t) = -7 / 12 * a ^ 3 := by
    rw [intervalIntegral.integral_congr_ae_restrict heq5]
    dsimp [p5]
    have h := integral_scaled_quadratic
      (a ^ 3) (-45 / 8) (9 / 4) (-1 / 4) 4 5
    convert h using 1 <;> ring
  have hv6 : (∫ t in (5 : ℝ)..6, f t) = -11 / 12 * a ^ 3 := by
    rw [intervalIntegral.integral_congr_ae_restrict heq6]
    dsimp [p6]
    have h := integral_scaled_quadratic
      (a ^ 3) (53 / 8) (-11 / 4) (1 / 4) 5 6
    convert h using 1 <;> ring
  have hf12 : IntervalIntegrable f volume 0 2 := hf1.trans hf2
  have hf123 : IntervalIntegrable f volume 0 3 := hf12.trans hf3
  have hf1234 : IntervalIntegrable f volume 0 4 := hf123.trans hf4
  have hf12345 : IntervalIntegrable f volume 0 5 := hf1234.trans hf5
  unfold lineIntegral
  change (∫ t in (0 : ℝ)..6, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hf12345 hf6,
    ← intervalIntegral.integral_add_adjacent_intervals hf1234 hf5,
    ← intervalIntegral.integral_add_adjacent_intervals hf123 hf4,
    ← intervalIntegral.integral_add_adjacent_intervals hf12 hf3,
    ← intervalIntegral.integral_add_adjacent_intervals hf1 hf2,
    hv1, hv2, hv3, hv4, hv5, hv6]
  ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    projectedArea a = 3 / 4 * a ^ 2 := by
  exact projectedArea_formula a ha

theorem gap5 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = stokesSurfaceFlux a := by
  rw [lineIntegral_formula, stokesSurfaceFlux_eq_area,
    projectedArea_formula a ha]
  ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = -6 * a * projectedArea a := by
  rw [lineIntegral_formula, projectedArea_formula a ha]
  ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = -(9 / 2) * a ^ 3 := by
  exact lineIntegral_formula a

end

end ProofGap.Exercise4373
