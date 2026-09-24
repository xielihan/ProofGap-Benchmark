import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Defs.Filter

open scoped Interval

namespace ProofGap.Exercise2501

noncomputable section

def upperSemicircle (a x : ℝ) : ℝ := Real.sqrt (a ^ 2 - x ^ 2)

def speed (a x : ℝ) : ℝ :=
  Real.sqrt (1 + deriv (upperSemicircle a) x ^ 2)

def firstMoment (a : ℝ) : ℝ :=
  ∫ x in -a..a,
    upperSemicircle a x * (a / Real.sqrt (a ^ 2 - x ^ 2))

def secondMoment (a : ℝ) : ℝ :=
  ∫ x in -a..a,
    (a ^ 2 - x ^ 2) * (a / Real.sqrt (a ^ 2 - x ^ 2))

private abbrev volume : MeasureTheory.Measure ℝ := MeasureTheory.volume

private theorem intervalIntegral.integral_add_adjacent
    {f : ℝ → ℝ} {a b c : ℝ}
    (hab : IntervalIntegrable f volume a b)
    (hbc : IntervalIntegrable f volume b c) :
    (∫ x in a..b, f x) + (∫ x in b..c, f x) = ∫ x in a..c, f x :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

private theorem intervalIntegral.integral_sqrt_sq_sub_sq
    (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -a..a, Real.sqrt (a ^ 2 - x ^ 2)) =
      Real.pi * a ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => Real.sqrt (a ^ 2 - x ^ 2)
  let g : ℝ → ℝ := fun t => a * Real.sin t
  have hf : Continuous f := by
    dsimp [f]
    exact Real.continuous_sqrt.comp
      ((continuous_const.pow 2).sub (continuous_id.pow 2))
  have hneg : IntervalIntegrable f volume (-a) 0 :=
    hf.intervalIntegrable _ _
  have hpos : IntervalIntegrable f volume 0 a :=
    hf.intervalIntegrable _ _
  have hreflect :
      (∫ x in 0..a, f (-x)) = ∫ x in -a..0, f x := by
    simpa using
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := a))
  have heven : (∫ x in -a..0, f x) = ∫ x in 0..a, f x := by
    rw [← hreflect]
    apply intervalIntegral.integral_congr
    intro x _
    simp [f]
  have hadd :
      (∫ x in -a..0, f x) + (∫ x in 0..a, f x) =
        ∫ x in -a..a, f x :=
    intervalIntegral.integral_add_adjacent hneg hpos
  have hfull :
      (∫ x in -a..a, f x) = 2 * ∫ x in 0..a, f x := by
    rw [← hadd, heven]
    ring
  have hg : ∀ t : ℝ, HasDerivAt g (a * Real.cos t) t := by
    intro t
    dsimp [g]
    exact (Real.hasDerivAt_sin t).const_mul a
  let H : ℝ → ℝ := fun y => ∫ x in 0..y, f x
  have hH : ∀ y : ℝ, HasDerivAt H (f y) y := by
    intro y
    have hyInt : IntervalIntegrable f volume 0 y :=
      hf.intervalIntegrable 0 y
    have hyCont : ContinuousAt f y := hf.continuousAt
    have hyMeas : StronglyMeasurableAtFilter f (nhds y) volume :=
      hf.stronglyMeasurable.stronglyMeasurableAtFilter
    simpa [H] using
      (intervalIntegral.integral_hasDerivAt_right hyInt hyMeas hyCont)
  have hKderiv : ∀ t : ℝ,
      HasDerivAt (fun y => H (g y))
        (f (g t) * (a * Real.cos t)) t := by
    intro t
    exact (hH (g t)).comp t (hg t)
  have hgcont : Continuous g := by
    dsimp [g]
    exact continuous_const.mul Real.continuous_sin
  have hweight : Continuous (fun t : ℝ => a * Real.cos t) :=
    continuous_const.mul Real.continuous_cos
  have htransInt :
      IntervalIntegrable
        (fun t : ℝ => f (g t) * (a * Real.cos t)) volume
        0 (Real.pi / 2) :=
    ((hf.comp hgcont).mul hweight).intervalIntegrable _ _
  have hsub' :
      (∫ t in 0..Real.pi / 2, f (g t) * (a * Real.cos t)) =
        ∫ x in 0..a, f x := by
    calc
      (∫ t in 0..Real.pi / 2, f (g t) * (a * Real.cos t)) =
          H (g (Real.pi / 2)) - H (g 0) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hKderiv t) htransInt
      _ = ∫ x in 0..a, f x := by
        simp [H, g]
  have htransform :
      (∫ x in 0..a, f x) =
        ∫ t in 0..Real.pi / 2, (a * Real.cos t) ^ 2 := by
    rw [← hsub']
    apply intervalIntegral.integral_congr
    intro t ht
    have hpi : (0 : ℝ) ≤ Real.pi / 2 := by
      linarith [Real.pi_pos]
    change min (0 : ℝ) (Real.pi / 2) ≤ t ∧
      t ≤ max (0 : ℝ) (Real.pi / 2) at ht
    rw [min_eq_left hpi, max_eq_right hpi] at ht
    have hcos : 0 ≤ Real.cos t := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · linarith [ht.1, Real.pi_pos]
      · exact ht.2
    have hrad :
        a ^ 2 - (a * Real.sin t) ^ 2 = (a * Real.cos t) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    change f (g t) * (a * Real.cos t) = (a * Real.cos t) ^ 2
    dsimp [f, g]
    rw [hrad, Real.sqrt_sq (mul_nonneg ha hcos)]
    ring
  let F : ℝ → ℝ := fun t => (t + Real.sin t * Real.cos t) / 2
  have hFderiv : ∀ t : ℝ, HasDerivAt F (Real.cos t ^ 2) t := by
    intro t
    have hid : HasDerivAt (fun y : ℝ => y) 1 t := by
      simpa [id] using hasDerivAt_id t
    have hprod :
        HasDerivAt (fun y : ℝ => Real.sin y * Real.cos y)
          (Real.cos t * Real.cos t + Real.sin t * (-Real.sin t)) t :=
      (Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)
    have hsum := hid.add hprod
    have hdiv := hsum.div_const 2
    dsimp [F]
    convert hdiv using 1
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hcosInt :
      (∫ t in 0..Real.pi / 2, Real.cos t ^ 2) = Real.pi / 4 := by
    have hint :
        IntervalIntegrable (fun t : ℝ => Real.cos t ^ 2) volume
          0 (Real.pi / 2) :=
      (Real.continuous_cos.pow 2).intervalIntegrable _ _
    calc
      (∫ t in 0..Real.pi / 2, Real.cos t ^ 2) =
          F (Real.pi / 2) - F 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hFderiv t) hint
      _ = Real.pi / 4 := by
        dsimp [F]
        rw [Real.cos_pi_div_two]
        simp
        ring
  have hquarter :
      (∫ x in 0..a, f x) = Real.pi * a ^ 2 / 4 := by
    calc
      (∫ x in 0..a, f x) =
          ∫ t in 0..Real.pi / 2, (a * Real.cos t) ^ 2 := htransform
      _ = a ^ 2 * ∫ t in 0..Real.pi / 2, Real.cos t ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = Real.pi * a ^ 2 / 4 := by
        rw [hcosInt]
        ring
  calc
    (∫ x in -a..a, Real.sqrt (a ^ 2 - x ^ 2)) =
        ∫ x in -a..a, f x := by rfl
    _ = 2 * ∫ x in 0..a, f x := hfull
    _ = Real.pi * a ^ 2 / 2 := by
      rw [hquarter]
      ring

theorem gap1 (a x : ℝ) :
    speed a x = Real.sqrt (1 + deriv (upperSemicircle a) x ^ 2) := by
  rfl

theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    speed a x = a / upperSemicircle a x := by
  have hax : -a < x ∧ x < a := by
    simpa [abs_lt] using hx
  have hleft : 0 < a - x := sub_pos.mpr hax.2
  have hright : 0 < a + x := by
    linarith [hax.1]
  have hprod : 0 < (a - x) * (a + x) := mul_pos hleft hright
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    nlinarith [hprod]
  have hspos : 0 < Real.sqrt (a ^ 2 - x ^ 2) := Real.sqrt_pos.2 hrad
  have hsne : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 := ne_of_gt hspos
  have hs_sq : Real.sqrt (a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 :=
    Real.sq_sqrt hrad.le
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 2
  have hinner :
      HasDerivAt (fun y : ℝ => a ^ 2 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (a ^ 2)).sub hsq using 1 <;> ring
  have hcomp :
      HasDerivAt (fun y : ℝ => Real.sqrt (a ^ 2 - y ^ 2))
        (-x / Real.sqrt (a ^ 2 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt hrad.ne').comp x hinner using 1 <;>
      field_simp [hsne] <;> ring
  have hderiv :
      deriv (upperSemicircle a) x =
        -x / Real.sqrt (a ^ 2 - x ^ 2) := by
    unfold upperSemicircle
    exact hcomp.deriv
  rw [gap1, hderiv]
  unfold upperSemicircle
  have hquot : 0 ≤ a / Real.sqrt (a ^ 2 - x ^ 2) :=
    div_nonneg ha.le (Real.sqrt_nonneg _)
  calc
    Real.sqrt
        (1 + (-x / Real.sqrt (a ^ 2 - x ^ 2)) ^ 2) =
      Real.sqrt ((a / Real.sqrt (a ^ 2 - x ^ 2)) ^ 2) := by
        congr 1
        field_simp [hsne]
        nlinarith [hs_sq]
    _ = a / Real.sqrt (a ^ 2 - x ^ 2) := Real.sqrt_sq hquot

theorem gap3 (a x : ℝ) :
    a / upperSemicircle a x = a / Real.sqrt (a ^ 2 - x ^ 2) := by
  rfl

theorem gap4 (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    speed a x = a / Real.sqrt (a ^ 2 - x ^ 2) := by
  rw [gap2 a x ha hx]
  exact gap3 a x

theorem gap5 (a M₁ : ℝ) (hM : M₁ = firstMoment a) :
    M₁ = ∫ x in -a..a,
      Real.sqrt (a ^ 2 - x ^ 2) *
        (a / Real.sqrt (a ^ 2 - x ^ 2)) := by
  simpa [firstMoment, upperSemicircle] using hM

theorem gap6 (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -a..a,
      Real.sqrt (a ^ 2 - x ^ 2) *
        (a / Real.sqrt (a ^ 2 - x ^ 2))) = 2 * a ^ 2 := by
  have hab : -a ≤ a := by linarith
  have hne : ∀ᵐ x ∂volume, x ≠ a := by
    rw [MeasureTheory.ae_iff]
    simp
  calc
    (∫ x in -a..a,
      Real.sqrt (a ^ 2 - x ^ 2) *
        (a / Real.sqrt (a ^ 2 - x ^ 2))) =
        ∫ _x in -a..a, a := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hne] with x hxa hx
      have hx' : x ∈ Set.Ioc (-a) a := by
        simpa [Set.uIoc, hab] using hx
      have hxa' : x < a := lt_of_le_of_ne hx'.2 hxa
      have hleft : 0 < a - x := sub_pos.mpr hxa'
      have hright : 0 < a + x := by
        linarith [hx'.1]
      have hprod : 0 < (a - x) * (a + x) := mul_pos hleft hright
      have hrad : 0 < a ^ 2 - x ^ 2 := by
        nlinarith [hprod]
      have hsne : Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hrad)
      field_simp [hsne]
    _ = 2 * a ^ 2 := by
      simp
      ring

theorem gap7 (a M₁ : ℝ) (ha : 0 ≤ a) (hM : M₁ = firstMoment a) :
    M₁ = 2 * a ^ 2 := by
  calc
    M₁ = ∫ x in -a..a,
        Real.sqrt (a ^ 2 - x ^ 2) *
          (a / Real.sqrt (a ^ 2 - x ^ 2)) := gap5 a M₁ hM
    _ = 2 * a ^ 2 := gap6 a ha

theorem gap8 (a M₂ : ℝ) (hM : M₂ = secondMoment a) :
    M₂ = ∫ x in -a..a,
      (a ^ 2 - x ^ 2) * (a / Real.sqrt (a ^ 2 - x ^ 2)) := by
  simpa [secondMoment] using hM

theorem gap9 (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -a..a,
      (a ^ 2 - x ^ 2) * (a / Real.sqrt (a ^ 2 - x ^ 2))) =
        2 * a * ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := by
  let f : ℝ → ℝ := fun x => Real.sqrt (a ^ 2 - x ^ 2)
  have hab : -a ≤ a := by linarith
  have hcont : Continuous f := by
    dsimp [f]
    exact Real.continuous_sqrt.comp
      ((continuous_const.pow 2).sub (continuous_id.pow 2))
  have hneg : IntervalIntegrable f volume (-a) 0 :=
    hcont.intervalIntegrable _ _
  have hpos : IntervalIntegrable f volume 0 a :=
    hcont.intervalIntegrable _ _
  have hreflect :
      (∫ x in 0..a, f (-x)) = ∫ x in -a..0, f x := by
    simpa using
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := a))
  have heven : (∫ x in -a..0, f x) = ∫ x in 0..a, f x := by
    rw [← hreflect]
    apply intervalIntegral.integral_congr
    intro x _
    simp [f]
  have hadd :
      (∫ x in -a..0, f x) + (∫ x in 0..a, f x) =
        ∫ x in -a..a, f x :=
    intervalIntegral.integral_add_adjacent hneg hpos
  calc
    (∫ x in -a..a,
      (a ^ 2 - x ^ 2) *
        (a / Real.sqrt (a ^ 2 - x ^ 2))) =
        ∫ x in -a..a, a * f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (-a) a := by
        simpa [Set.uIcc, hab] using hx
      have hprod : 0 ≤ (a - x) * (a + x) :=
        mul_nonneg (sub_nonneg.mpr hx'.2) (by linarith [hx'.1])
      have hrad : 0 ≤ a ^ 2 - x ^ 2 := by
        nlinarith [hprod]
      have hs_sq : f x ^ 2 = a ^ 2 - x ^ 2 := by
        simpa [f] using Real.sq_sqrt hrad
      change (a ^ 2 - x ^ 2) * (a / f x) = a * f x
      rw [← hs_sq]
      by_cases hs : f x = 0
      · simp [hs]
      · field_simp [hs] <;> ring
    _ = a * ∫ x in -a..a, f x := by
      rw [intervalIntegral.integral_const_mul]
    _ = a * ((∫ x in -a..0, f x) + ∫ x in 0..a, f x) := by
      rw [hadd]
    _ = 2 * a * ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := by
      rw [heven]
      dsimp [f]
      ring

theorem gap10 (a : ℝ) (ha : 0 ≤ a) :
    2 * a * (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) =
      Real.pi * a ^ 3 / 2 := by
  let f : ℝ → ℝ := fun x => Real.sqrt (a ^ 2 - x ^ 2)
  have hcont : Continuous f := by
    dsimp [f]
    exact Real.continuous_sqrt.comp
      ((continuous_const.pow 2).sub (continuous_id.pow 2))
  have hneg : IntervalIntegrable f volume (-a) 0 :=
    hcont.intervalIntegrable _ _
  have hpos : IntervalIntegrable f volume 0 a :=
    hcont.intervalIntegrable _ _
  have hreflect :
      (∫ x in 0..a, f (-x)) = ∫ x in -a..0, f x := by
    simpa using
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := a))
  have heven : (∫ x in -a..0, f x) = ∫ x in 0..a, f x := by
    rw [← hreflect]
    apply intervalIntegral.integral_congr
    intro x _
    simp [f]
  have hadd :
      (∫ x in -a..0, f x) + (∫ x in 0..a, f x) =
        ∫ x in -a..a, f x :=
    intervalIntegral.integral_add_adjacent hneg hpos
  have hfull :
      (∫ x in -a..a, f x) = 2 * ∫ x in 0..a, f x := by
    rw [← hadd, heven]
    ring
  have hcircle :
      (∫ x in -a..a, f x) = Real.pi * a ^ 2 / 2 := by
    simpa [f, mul_comm, mul_left_comm, mul_assoc] using
      (intervalIntegral.integral_sqrt_sq_sub_sq (a := a) ha)
  calc
    2 * a * (∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2)) =
        a * (2 * ∫ x in 0..a, f x) := by
      dsimp [f]
      ring
    _ = a * (∫ x in -a..a, f x) := by rw [hfull]
    _ = a * (Real.pi * a ^ 2 / 2) := by rw [hcircle]
    _ = Real.pi * a ^ 3 / 2 := by ring

theorem gap11 (a M₂ : ℝ) (ha : 0 ≤ a) (hM : M₂ = secondMoment a) :
    M₂ = Real.pi * a ^ 3 / 2 := by
  calc
    M₂ = ∫ x in -a..a,
        (a ^ 2 - x ^ 2) *
          (a / Real.sqrt (a ^ 2 - x ^ 2)) := gap8 a M₂ hM
    _ = 2 * a * ∫ x in 0..a, Real.sqrt (a ^ 2 - x ^ 2) := gap9 a ha
    _ = Real.pi * a ^ 3 / 2 := gap10 a ha

end

end ProofGap.Exercise2501
