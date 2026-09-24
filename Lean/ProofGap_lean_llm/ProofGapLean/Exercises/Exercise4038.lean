import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4038

noncomputable section

open MeasureTheory
open scoped Interval

def upperHeight (a x y : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2)

def upperDx (a x y : ℝ) : ℝ :=
  -x / upperHeight a x y

def upperDy (a x y : ℝ) : ℝ :=
  -y / upperHeight a x y

def rawAreaFactor (a x y : ℝ) : ℝ :=
  Real.sqrt (1 + upperDx a x y ^ 2 + upperDy a x y ^ 2)

def areaFactor (a x y : ℝ) : ℝ :=
  a / Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2)

def baseRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 / a ^ 2 + p.2 ^ 2 / b ^ 2 ≤ 1}

def quarterDomain (a b : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 ≤ p.1 ∧ p.1 ≤ a ∧
      0 ≤ p.2 ∧ p.2 ≤ b / a * Real.sqrt (a ^ 2 - p.1 ^ 2)}

def endpointPrimitive (a x y : ℝ) : ℝ :=
  Real.arcsin (y / Real.sqrt (a ^ 2 - x ^ 2))

def surfaceArea (a b : ℝ) : ℝ :=
  2 * ∫ p in baseRegion a b, areaFactor a p.1 p.2

theorem gap1 (a x y : ℝ) (ha : 0 < a)
    (hxy : x ^ 2 + y ^ 2 < a ^ 2) :
    rawAreaFactor a x y =
      Real.sqrt
        (1 + x ^ 2 / upperHeight a x y ^ 2 +
          y ^ 2 / upperHeight a x y ^ 2) := by
  simp only [rawAreaFactor, upperDx, upperDy, div_pow, neg_sq]

theorem gap2 (a x y : ℝ) (ha : 0 < a)
    (hxy : x ^ 2 + y ^ 2 < a ^ 2) :
    Real.sqrt
        (1 + x ^ 2 / upperHeight a x y ^ 2 +
          y ^ 2 / upperHeight a x y ^ 2) =
      Real.sqrt
        ((x ^ 2 + y ^ 2 + upperHeight a x y ^ 2) /
          upperHeight a x y ^ 2) := by
  have hD : 0 < a ^ 2 - x ^ 2 - y ^ 2 := by linarith
  have hh :
      upperHeight a x y ^ 2 = a ^ 2 - x ^ 2 - y ^ 2 := by
    simp only [upperHeight, Real.sq_sqrt hD.le]
  congr 1
  rw [hh]
  field_simp [hD.ne']
  ring

theorem gap3 (a x y : ℝ) (ha : 0 < a)
    (hxy : x ^ 2 + y ^ 2 < a ^ 2) :
    Real.sqrt
        ((x ^ 2 + y ^ 2 + upperHeight a x y ^ 2) /
          upperHeight a x y ^ 2) =
      areaFactor a x y := by
  have hD : 0 < a ^ 2 - x ^ 2 - y ^ 2 := by linarith
  have hh :
      upperHeight a x y ^ 2 = a ^ 2 - x ^ 2 - y ^ 2 := by
    simp only [upperHeight, Real.sq_sqrt hD.le]
  rw [hh]
  have hnum :
      x ^ 2 + y ^ 2 + (a ^ 2 - x ^ 2 - y ^ 2) = a ^ 2 := by
    ring
  rw [hnum, Real.sqrt_div (sq_nonneg a), Real.sqrt_sq_eq_abs,
    abs_of_pos ha]
  rfl

theorem gap4 (a x y : ℝ) (ha : 0 < a)
    (hxy : x ^ 2 + y ^ 2 < a ^ 2) :
    rawAreaFactor a x y = areaFactor a x y := by
  rw [gap1 a x y ha hxy, gap2 a x y ha hxy,
    gap3 a x y ha hxy]

theorem gap5 (a b x y : ℝ) (hp : (x, y) ∈ quarterDomain a b) :
    0 ≤ x := by
  exact hp.1

theorem gap6 (a b x y : ℝ) (hp : (x, y) ∈ quarterDomain a b) :
    x ≤ a := by
  exact hp.2.1

theorem gap7 (a b x y : ℝ) (hp : (x, y) ∈ quarterDomain a b) :
    0 ≤ y := by
  exact hp.2.2.1

theorem gap8 (a b x y : ℝ) (hp : (x, y) ∈ quarterDomain a b) :
    y ≤ b / a * Real.sqrt (a ^ 2 - x ^ 2) := by
  exact hp.2.2.2

private def invCircleWeight (u : ℝ) : ℝ :=
  (Real.sqrt (1 - u ^ 2))⁻¹

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

private theorem invCircleWeight_intervalIntegrable
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable invCircleWeight volume 0 c := by
  have hfull :
      IntervalIntegrable invCircleWeight volume (-1 : ℝ) 1 := by
    simpa [invCircleWeight] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  exact hfull.mono_set (by
    rw [Set.uIcc_of_le hc0, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)

private theorem integral_invCircleWeight
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ u in (0 : ℝ)..c, invCircleWeight u) =
      Real.arcsin c - Real.arcsin 0 := by
  have hint := invCircleWeight_intervalIntegrable c hc0 hc1
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hc0 Real.continuous_arcsin.continuousOn
  · intro u hu
    have hneg : u ≠ -1 := by linarith [hu.1]
    have hone : u ≠ 1 := by linarith [hu.2, hc1]
    simpa [invCircleWeight, one_div] using
      (Real.hasDerivAt_arcsin hneg hone).hasDerivWithinAt
  · exact hint

private theorem scaled_slice_intervalIntegrable
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable
      (fun y : ℝ => a / Real.sqrt (s ^ 2 - y ^ 2))
      volume 0 (c * s) := by
  have hbase := invCircleWeight_intervalIntegrable c hc0 hc1
  have hscaled :
      IntervalIntegrable
        (fun y : ℝ => invCircleWeight ((1 / s) * y))
        volume 0 (c * s) := by
    have h :=
      hbase.comp_mul_left (c := (1 / s))
    convert h using 1 <;> field_simp [hs.ne'] <;> ring
  have hmul :=
    hscaled.const_mul (a / s)
  refine hmul.congr ?_
  intro y hy
  change
    a / s * invCircleWeight ((1 / s) * y) =
      a / Real.sqrt (s ^ 2 - y ^ 2)
  have hid :
      s ^ 2 - y ^ 2 =
        s ^ 2 * (1 - ((1 / s) * y) ^ 2) := by
    field_simp [hs.ne']
  rw [hid, Real.sqrt_mul (sq_nonneg s),
    Real.sqrt_sq hs.le]
  dsimp [invCircleWeight]
  field_simp [hs.ne']

private theorem scaled_slice_integral
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ y in (0 : ℝ)..c * s,
        a / Real.sqrt (s ^ 2 - y ^ 2)) =
      a * (Real.arcsin c - Real.arcsin 0) := by
  have heq :
      (∫ y in (0 : ℝ)..c * s,
          a / Real.sqrt (s ^ 2 - y ^ 2)) =
        ∫ y in (0 : ℝ)..c * s,
          (a / s) * invCircleWeight ((1 / s) * y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    change
      a / Real.sqrt (s ^ 2 - y ^ 2) =
        a / s * invCircleWeight ((1 / s) * y)
    have hid :
        s ^ 2 - y ^ 2 =
          s ^ 2 * (1 - ((1 / s) * y) ^ 2) := by
      field_simp [hs.ne']
    rw [hid, Real.sqrt_mul (sq_nonneg s),
      Real.sqrt_sq hs.le]
    dsimp [invCircleWeight]
    field_simp [hs.ne']
  have hchange :
      (1 / s) *
          (∫ y in (0 : ℝ)..c * s,
            invCircleWeight ((1 / s) * y)) =
        ∫ u in (0 : ℝ)..c, invCircleWeight u := by
    convert
      (intervalIntegral.mul_integral_comp_mul_left
        (f := invCircleWeight) (c := (1 / s))
        (a := (0 : ℝ)) (b := c * s)) using 1 <;>
      field_simp [hs.ne'] <;> ring
  rw [heq, intervalIntegral.integral_const_mul]
  calc
    a / s *
          (∫ y in (0 : ℝ)..c * s,
            invCircleWeight ((1 / s) * y)) =
        a *
          ((1 / s) *
            ∫ y in (0 : ℝ)..c * s,
              invCircleWeight ((1 / s) * y)) := by ring
    _ = a * (∫ u in (0 : ℝ)..c, invCircleWeight u) := by
      rw [hchange]
    _ = a * (Real.arcsin c - Real.arcsin 0) := by
      rw [integral_invCircleWeight c hc0 hc1]

private theorem scaled_symmetric_slice_intervalIntegrable
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable
      (fun y : ℝ => a / Real.sqrt (s ^ 2 - y ^ 2))
      volume (-(c * s)) (c * s) := by
  have hbase :
      IntervalIntegrable invCircleWeight volume (-c) c := by
    have hfull :
        IntervalIntegrable invCircleWeight volume (-1 : ℝ) 1 := by
      simpa [invCircleWeight] using
        Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
    refine hfull.mono_set ?_
    rw [Set.uIcc_of_le (by linarith),
      Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    intro u hu
    exact ⟨by linarith [hu.1, hc1], by linarith [hu.2, hc1]⟩
  have hscaled :
      IntervalIntegrable
        (fun y : ℝ => invCircleWeight ((1 / s) * y))
        volume (-(c * s)) (c * s) := by
    have h := hbase.comp_mul_left (c := (1 / s))
    convert h using 1 <;> field_simp [hs.ne'] <;> ring
  have hmul := hscaled.const_mul (a / s)
  refine hmul.congr ?_
  intro y hy
  change
    a / s * invCircleWeight ((1 / s) * y) =
      a / Real.sqrt (s ^ 2 - y ^ 2)
  have hid :
      s ^ 2 - y ^ 2 =
        s ^ 2 * (1 - ((1 / s) * y) ^ 2) := by
    field_simp [hs.ne']
  rw [hid, Real.sqrt_mul (sq_nonneg s),
    Real.sqrt_sq hs.le]
  dsimp [invCircleWeight]
  field_simp [hs.ne']

private theorem scaled_symmetric_slice_integral
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ y in -(c * s)..c * s,
        a / Real.sqrt (s ^ 2 - y ^ 2)) =
      2 * a * (Real.arcsin c - Real.arcsin 0) := by
  let f : ℝ → ℝ :=
    fun y => a / Real.sqrt (s ^ 2 - y ^ 2)
  have hfull :
      IntervalIntegrable f volume (-(c * s)) (c * s) := by
    simpa [f] using
      scaled_symmetric_slice_intervalIntegrable a s c hs hc0 hc1
  have hcs : 0 ≤ c * s := mul_nonneg hc0 hs.le
  have hleft : IntervalIntegrable f volume (-(c * s)) 0 :=
    hfull.mono_set (by
      rw [Set.uIcc_of_le (neg_nonpos.2 hcs),
        Set.uIcc_of_le (by linarith : -(c * s) ≤ c * s)]
      intro y hy
      exact ⟨hy.1, hy.2.trans hcs⟩)
  have hright : IntervalIntegrable f volume 0 (c * s) :=
    scaled_slice_intervalIntegrable a s c hs hc0 hc1
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ y in -(c * s)..(0 : ℝ), f y) =
        ∫ y in (0 : ℝ)..c * s, f y := by
    calc
      (∫ y in -(c * s)..(0 : ℝ), f y) =
          ∫ y in (0 : ℝ)..c * s, f (-y) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := c * s)).symm
      _ = ∫ y in (0 : ℝ)..c * s, f y := by
        apply intervalIntegral.integral_congr
        intro y hy
        dsimp [f]
        congr 2
        ring
  rw [← hsplit, hreflect]
  dsimp [f]
  have hdouble :
      (∫ y in (0 : ℝ)..c * s,
          a / Real.sqrt (s ^ 2 - y ^ 2)) +
        ∫ y in (0 : ℝ)..c * s,
          a / Real.sqrt (s ^ 2 - y ^ 2) =
        2 *
          ∫ y in (0 : ℝ)..c * s,
            a / Real.sqrt (s ^ 2 - y ^ 2) := by
    ring
  rw [hdouble]
  rw [scaled_slice_integral a s c hs hc0 hc1]
  ring

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

private theorem mem_baseRegion_iff_slices
    (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (x, y) ∈ baseRegion a b ↔
      x ∈ Set.Icc (-a) a ∧
        y ∈
          Set.Icc
            (-(b / a * Real.sqrt (a ^ 2 - x ^ 2)))
            (b / a * Real.sqrt (a ^ 2 - x ^ 2)) := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hab2 : 0 < a ^ 2 * b ^ 2 := mul_pos ha2 hb2
  have hfrac :
      x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 =
        (b ^ 2 * x ^ 2 + a ^ 2 * y ^ 2) /
          (a ^ 2 * b ^ 2) := by
    field_simp [ha.ne', hb.ne']
  constructor
  · intro hp
    change x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 ≤ 1 at hp
    rw [hfrac] at hp
    have hpoly :
        b ^ 2 * x ^ 2 + a ^ 2 * y ^ 2 ≤
          a ^ 2 * b ^ 2 :=
      (div_le_one hab2).1 hp
    have hxSq : x ^ 2 ≤ a ^ 2 := by
      nlinarith
        [mul_nonneg (sq_nonneg a) (sq_nonneg y),
          hb2]
    have hxabs : |x| ≤ a := by
      rw [← sq_le_sq₀ (abs_nonneg x) ha.le, sq_abs]
      exact hxSq
    have hD : 0 ≤ a ^ 2 - x ^ 2 := by linarith
    have hs2 :
        Real.sqrt (a ^ 2 - x ^ 2) ^ 2 =
          a ^ 2 - x ^ 2 :=
      Real.sq_sqrt hD
    have hay :
        a ^ 2 * y ^ 2 ≤ b ^ 2 * (a ^ 2 - x ^ 2) := by
      nlinarith [hpoly]
    have hySq :
        y ^ 2 ≤ (b / a) ^ 2 * (a ^ 2 - x ^ 2) := by
      rw [div_pow, div_mul_eq_mul_div]
      exact (le_div_iff₀ ha2).2 (by
        simpa [mul_comm] using hay)
    have hright :
        0 ≤ b / a * Real.sqrt (a ^ 2 - x ^ 2) :=
      mul_nonneg (div_nonneg hb.le ha.le) (Real.sqrt_nonneg _)
    have hyabs :
        |y| ≤ b / a * Real.sqrt (a ^ 2 - x ^ 2) := by
      rw [← sq_le_sq₀ (abs_nonneg y) hright, sq_abs,
        mul_pow, hs2]
      exact hySq
    exact ⟨abs_le.1 hxabs, abs_le.1 hyabs⟩
  · rintro ⟨hx, hy⟩
    have hxabs : |x| ≤ a := abs_le.2 hx
    have hxSq : x ^ 2 ≤ a ^ 2 := by
      rw [← sq_abs x]
      exact (sq_le_sq₀ (abs_nonneg x) ha.le).2 hxabs
    have hD : 0 ≤ a ^ 2 - x ^ 2 := by linarith
    have hs2 :
        Real.sqrt (a ^ 2 - x ^ 2) ^ 2 =
          a ^ 2 - x ^ 2 :=
      Real.sq_sqrt hD
    have hright :
        0 ≤ b / a * Real.sqrt (a ^ 2 - x ^ 2) :=
      mul_nonneg (div_nonneg hb.le ha.le) (Real.sqrt_nonneg _)
    have hyabs :
        |y| ≤ b / a * Real.sqrt (a ^ 2 - x ^ 2) :=
      abs_le.2 hy
    have hySq :
        y ^ 2 ≤
          (b / a * Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 := by
      rw [← sq_abs y]
      exact
        (sq_le_sq₀ (abs_nonneg y) hright).2 hyabs
    have hmul :=
      mul_le_mul_of_nonneg_left hySq (sq_nonneg a)
    have hident :
        a ^ 2 *
            (b / a * Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 =
          b ^ 2 * (a ^ 2 - x ^ 2) := by
      rw [mul_pow, hs2, div_pow]
      field_simp [ha.ne']
    rw [hident] at hmul
    have hbx :=
      mul_le_mul_of_nonneg_left hxSq (sq_nonneg b)
    have hpoly :
        b ^ 2 * x ^ 2 + a ^ 2 * y ^ 2 ≤
          a ^ 2 * b ^ 2 := by
      nlinarith
    change x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 ≤ 1
    rw [hfrac]
    exact (div_le_one hab2).2 hpoly

private theorem integral_even_neg_pos
    (f : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hint : IntervalIntegrable f volume (-A) A)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x in -A..A, f x) =
      2 * ∫ x in (0 : ℝ)..A, f x := by
  have hleft : IntervalIntegrable f volume (-A) 0 :=
    hint.mono_set (by
      rw [Set.uIcc_of_le (neg_nonpos.2 hA),
        Set.uIcc_of_le (by linarith : -A ≤ A)]
      intro x hx
      exact ⟨hx.1, hx.2.trans hA⟩)
  have hright : IntervalIntegrable f volume 0 A :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hA,
        Set.uIcc_of_le (by linarith : -A ≤ A)]
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ x in -A..(0 : ℝ), f x) =
        ∫ x in (0 : ℝ)..A, f x := by
    calc
      (∫ x in -A..(0 : ℝ), f x) =
          ∫ x in (0 : ℝ)..A, f (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := A)).symm
      _ = ∫ x in (0 : ℝ)..A, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact heven x
  rw [← hsplit, hreflect]
  ring

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    surfaceArea a b =
      8 *
        ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..b / a * Real.sqrt (a ^ 2 - x ^ 2),
            areaFactor a x y := by
  let c : ℝ := b / a
  let d : ℝ → ℝ :=
    fun x => c * Real.sqrt (a ^ 2 - x ^ 2)
  let f : ℝ × ℝ → ℝ :=
    fun p => areaFactor a p.1 p.2
  let F : ℝ × ℝ → ℝ :=
    (baseRegion a b).indicator f
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg hb.le ha.le
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact (div_le_one ha).2 hba
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos hb ha
  have hregion : MeasurableSet (baseRegion a b) := by
    dsimp [baseRegion]
    measurability
  have hfmeas : Measurable f := by
    dsimp [f, areaFactor]
    measurability
  have hFstrong : StronglyMeasurable F := by
    dsimp [F]
    exact hfmeas.stronglyMeasurable.indicator hregion
  have hindicator (x y : ℝ) :
      F (x, y) =
        (Set.Icc (-a) a).indicator
          (fun x =>
            (Set.Icc (-(d x)) (d x)).indicator
              (fun y => areaFactor a x y) y) x := by
    have hmem :=
      mem_baseRegion_iff_slices a b x y ha hb
    change
      (baseRegion a b).indicator f (x, y) =
        (Set.Icc (-a) a).indicator
          (fun x =>
            (Set.Icc (-(d x)) (d x)).indicator
              (fun y => areaFactor a x y) y) x
    by_cases hp : (x, y) ∈ baseRegion a b
    · have hs := hmem.1 hp
      simp [hp, hs.1, hs.2, f, d, c]
    · have hs : ¬
          (x ∈ Set.Icc (-a) a ∧
            y ∈
              Set.Icc
                (-(b / a * Real.sqrt (a ^ 2 - x ^ 2)))
                (b / a * Real.sqrt (a ^ 2 - x ^ 2))) := by
        exact fun h => hp (hmem.2 h)
      by_cases hx : x ∈ Set.Icc (-a) a
      · have hy :
            y ∉
              Set.Icc
                (-(b / a * Real.sqrt (a ^ 2 - x ^ 2)))
                (b / a * Real.sqrt (a ^ 2 - x ^ 2)) :=
          fun h => hs ⟨hx, h⟩
        simp [hp, hx, hy, d, c]
      · simp [hp, hx]
  have hlineInt (x : ℝ) (hD : 0 < a ^ 2 - x ^ 2) :
      IntervalIntegrable (fun y : ℝ => areaFactor a x y)
        volume (-(d x)) (d x) := by
    let s : ℝ := Real.sqrt (a ^ 2 - x ^ 2)
    have hs : 0 < s := Real.sqrt_pos.2 hD
    have hs2 : s ^ 2 = a ^ 2 - x ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt hD.le
    change
      IntervalIntegrable
        (fun y : ℝ =>
          a / Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2))
        volume (-(c * s)) (c * s)
    have hraw :=
      scaled_symmetric_slice_intervalIntegrable
        a s c hs hc0 hc1
    refine hraw.congr ?_
    intro y hy
    rw [hs2]
  have hlineEval (x : ℝ) (hD : 0 < a ^ 2 - x ^ 2) :
      (∫ y in -(d x)..d x, areaFactor a x y) =
        2 * a * (Real.arcsin c - Real.arcsin 0) := by
    let s : ℝ := Real.sqrt (a ^ 2 - x ^ 2)
    have hs : 0 < s := Real.sqrt_pos.2 hD
    have hs2 : s ^ 2 = a ^ 2 - x ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt hD.le
    change
      (∫ y in -(c * s)..c * s,
        a / Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2)) =
          2 * a * (Real.arcsin c - Real.arcsin 0)
    calc
      (∫ y in -(c * s)..c * s,
          a / Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2)) =
          ∫ y in -(c * s)..c * s,
            a / Real.sqrt (s ^ 2 - y ^ 2) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [hs2]
      _ = 2 * a * (Real.arcsin c - Real.arcsin 0) :=
        scaled_symmetric_slice_integral
          a s c hs hc0 hc1
  have hsections :
      ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
        Integrable (fun y : ℝ => F (x, y)) := by
    filter_upwards [ae_real_ne (-a), ae_real_ne a] with x hxneg hxpos
    by_cases hx : x ∈ Set.Icc (-a) a
    · have hxleft : -a < x :=
        lt_of_le_of_ne hx.1 (Ne.symm hxneg)
      have hxright : x < a :=
        lt_of_le_of_ne hx.2 hxpos
      have hD : 0 < a ^ 2 - x ^ 2 := by
        nlinarith
          [mul_pos (sub_pos.2 hxright)
            (by linarith : 0 < a + x)]
      have hd0 : 0 ≤ d x :=
        mul_nonneg hc0 (Real.sqrt_nonneg _)
      have hline := hlineInt x hD
      have hlineOn :
          IntegrableOn (fun y : ℝ => areaFactor a x y)
            (Set.Icc (-(d x)) (d x)) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le
          (by linarith)).1 hline
      have hindLine :
          Integrable
            ((Set.Icc (-(d x)) (d x)).indicator
              (fun y : ℝ => areaFactor a x y)) :=
        (integrable_indicator_iff measurableSet_Icc).2 hlineOn
      have heq :
          (fun y : ℝ => F (x, y)) =
            (Set.Icc (-(d x)) (d x)).indicator
              (fun y : ℝ => areaFactor a x y) := by
        funext y
        rw [hindicator]
        simp [hx]
      rw [heq]
      exact hindLine
    · have heq : (fun y : ℝ => F (x, y)) = 0 := by
        funext y
        rw [hindicator]
        simp [hx]
      rw [heq]
      exact integrable_zero ℝ ℝ (volume : Measure ℝ)
  let C : ℝ :=
    2 * a * (Real.arcsin c - Real.arcsin 0)
  have hnormSection
      (x : ℝ) (hx : x ∈ Set.Icc (-a) a)
      (hD : 0 < a ^ 2 - x ^ 2) :
      (∫ y : ℝ, ‖F (x, y)‖) = C := by
    have hd0 : 0 ≤ d x :=
      mul_nonneg hc0 (Real.sqrt_nonneg _)
    have heq :
        (fun y : ℝ => F (x, y)) =
          (Set.Icc (-(d x)) (d x)).indicator
            (fun y : ℝ => areaFactor a x y) := by
      funext y
      rw [hindicator]
      simp [hx]
    calc
      (∫ y : ℝ, ‖F (x, y)‖) =
          ∫ y : ℝ,
            (Set.Icc (-(d x)) (d x)).indicator
              (fun y : ℝ => areaFactor a x y) y := by
        apply integral_congr_ae
        filter_upwards with y
        rw [show F (x, y) =
          (Set.Icc (-(d x)) (d x)).indicator
            (fun y : ℝ => areaFactor a x y) y by
              exact congrFun heq y]
        by_cases hy : y ∈ Set.Icc (-(d x)) (d x)
        · simp only [Set.indicator_of_mem hy, Real.norm_eq_abs]
          rw [abs_of_nonneg]
          exact div_nonneg ha.le (Real.sqrt_nonneg _)
        · simp [hy]
      _ = ∫ y in -(d x)..d x, areaFactor a x y :=
        integral_indicator_Icc_eq_interval
          (-(d x)) (d x) _ (by linarith)
      _ = C := by
        exact hlineEval x hD
  have houter :
      Integrable
        (fun x : ℝ => ∫ y : ℝ, ‖F (x, y)‖) := by
    have hC :
        Integrable
          ((Set.Icc (-a) a).indicator (fun _ : ℝ => C)) :=
      (integrable_indicator_iff measurableSet_Icc).2
        continuous_const.integrableOn_Icc
    refine hC.congr ?_
    filter_upwards [ae_real_ne (-a), ae_real_ne a] with x hxneg hxpos
    by_cases hx : x ∈ Set.Icc (-a) a
    · have hxleft : -a < x :=
        lt_of_le_of_ne hx.1 (Ne.symm hxneg)
      have hxright : x < a :=
        lt_of_le_of_ne hx.2 hxpos
      have hD : 0 < a ^ 2 - x ^ 2 := by
        nlinarith
          [mul_pos (sub_pos.2 hxright)
            (by linarith : 0 < a + x)]
      rw [Set.indicator_of_mem hx, hnormSection x hx hD]
    · rw [Set.indicator_of_notMem hx]
      have heq : (fun y : ℝ => F (x, y)) = 0 := by
        funext y
        rw [hindicator]
        simp [hx]
      have hnormzero : (fun y : ℝ => ‖F (x, y)‖) = 0 := by
        funext y
        rw [congrFun heq y]
        simp
      rw [hnormzero]
      simp
  have hind : Integrable F
      ((volume : Measure ℝ).prod volume) := by
    exact
      (integrable_prod_iff hFstrong.aestronglyMeasurable).2
        ⟨hsections, houter⟩
  have hslice :
      (∫ p in baseRegion a b, areaFactor a p.1 p.2) =
        ∫ x in -a..a,
          ∫ y in -(d x)..d x, areaFactor a x y := by
    rw [← integral_indicator hregion]
    change
      (∫ p : ℝ × ℝ, F p
        ∂((volume : Measure ℝ).prod volume)) = _
    rw [integral_prod _ hind]
    have hcollapse (x : ℝ) :
        (∫ y : ℝ,
          (Set.Icc (-a) a).indicator
            (fun x =>
              (Set.Icc (-(d x)) (d x)).indicator
                (fun y => areaFactor a x y) y) x) =
          (Set.Icc (-a) a).indicator
            (fun x =>
              ∫ y : ℝ,
                (Set.Icc (-(d x)) (d x)).indicator
                  (fun y => areaFactor a x y) y) x := by
      by_cases hx : x ∈ Set.Icc (-a) a <;> simp [hx]
    simp_rw [hindicator, hcollapse]
    rw [integral_indicator_Icc_eq_interval
      (-a) a _ (by linarith)]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)] at hx
    have hxSq : x ^ 2 ≤ a ^ 2 := by
      have hxabs : |x| ≤ a := abs_le.2 hx
      rw [← sq_abs x]
      exact (sq_le_sq₀ (abs_nonneg x) ha.le).2 hxabs
    have hd0 : 0 ≤ d x :=
      mul_nonneg hc0 (Real.sqrt_nonneg _)
    exact integral_indicator_Icc_eq_interval
      (-(d x)) (d x) _ (by linarith)
  let K : ℝ → ℝ :=
    fun x =>
      ∫ y in -(d x)..d x, areaFactor a x y
  let Q : ℝ → ℝ :=
    fun x =>
      ∫ y in (0 : ℝ)..d x, areaFactor a x y
  have hsectionEq
      (x : ℝ) (hx : x ∈ Set.Icc (-a) a) :
      (∫ y : ℝ, F (x, y)) = K x := by
    have hd0 : 0 ≤ d x :=
      mul_nonneg hc0 (Real.sqrt_nonneg _)
    have heq :
        (fun y : ℝ => F (x, y)) =
          (Set.Icc (-(d x)) (d x)).indicator
            (fun y : ℝ => areaFactor a x y) := by
      funext y
      rw [hindicator]
      simp [hx]
    rw [heq]
    exact integral_indicator_Icc_eq_interval
      (-(d x)) (d x) _ (by linarith)
  have hKint :
      IntervalIntegrable K volume (-a) a := by
    have hsecGlobal :
        Integrable (fun x : ℝ => ∫ y : ℝ, F (x, y)) :=
      hind.integral_prod_left
    have hsecInt :
        IntervalIntegrable
          (fun x : ℝ => ∫ y : ℝ, F (x, y))
          volume (-a) a :=
      hsecGlobal.intervalIntegrable
    refine hsecInt.congr ?_
    intro x hx
    rw [Set.uIoc_of_le (by linarith : -a ≤ a)] at hx
    exact hsectionEq x ⟨hx.1.le, hx.2⟩
  have hKeven : ∀ x : ℝ, K (-x) = K x := by
    intro x
    have hdneg : d (-x) = d x := by
      dsimp [d]
      congr 2
      ring
    dsimp [K]
    rw [hdneg]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp [areaFactor]
    congr 2
    ring
  have houterEven :
      (∫ x in -a..a, K x) =
        2 * ∫ x in (0 : ℝ)..a, K x :=
    integral_even_neg_pos K a ha.le hKint hKeven
  have hinnerEven
      (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) a) :
      K x = 2 * Q x := by
    rw [Set.uIcc_of_le ha.le] at hx
    rcases hx.2.eq_or_lt with hxa | hxa
    · subst x
      have hd : d a = 0 := by
        simp [d]
      simp [K, Q, hd]
    · have hD : 0 < a ^ 2 - x ^ 2 := by
        nlinarith
          [mul_pos (sub_pos.2 hxa)
            (add_pos_of_pos_of_nonneg ha hx.1)]
      have hd0 : 0 ≤ d x :=
        mul_nonneg hc0 (Real.sqrt_nonneg _)
      have hint := hlineInt x hD
      have heven :
          ∀ y : ℝ,
            areaFactor a x (-y) = areaFactor a x y := by
        intro y
        dsimp [areaFactor]
        congr 2
        ring
      exact
        integral_even_neg_pos
          (fun y : ℝ => areaFactor a x y)
          (d x) hd0 hint heven
  have hfullQuarter :
      (∫ x in -a..a, K x) =
        4 * ∫ x in (0 : ℝ)..a, Q x := by
    rw [houterEven]
    have hcongr :
        (∫ x in (0 : ℝ)..a, K x) =
          ∫ x in (0 : ℝ)..a, 2 * Q x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hinnerEven x hx
    rw [hcongr, intervalIntegral.integral_const_mul]
    ring
  rw [surfaceArea, hslice]
  change
    2 * (∫ x in -a..a, K x) =
      8 *
        ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..b / a *
            Real.sqrt (a ^ 2 - x ^ 2),
            areaFactor a x y
  rw [hfullQuarter]
  change
    2 * (4 * ∫ x in (0 : ℝ)..a, Q x) =
      8 * ∫ x in (0 : ℝ)..a, Q x
  ring

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    surfaceArea a b =
      8 * a *
        ∫ x in (0 : ℝ)..a,
          endpointPrimitive a x
              (b / a * Real.sqrt (a ^ 2 - x ^ 2)) -
            endpointPrimitive a x 0 := by
  have hc0 : 0 ≤ b / a := div_nonneg hb.le ha.le
  have hc1 : b / a ≤ 1 := (div_le_one ha).2 hba
  have hinner (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) a) :
      (∫ y in (0 : ℝ)..b / a * Real.sqrt (a ^ 2 - x ^ 2),
          areaFactor a x y) =
        a *
          (endpointPrimitive a x
              (b / a * Real.sqrt (a ^ 2 - x ^ 2)) -
            endpointPrimitive a x 0) := by
    rw [Set.uIcc_of_le ha.le] at hx
    rcases hx.2.eq_or_lt with hxa | hxa
    · subst x
      simp [endpointPrimitive]
    · have hD : 0 < a ^ 2 - x ^ 2 := by
        nlinarith
          [mul_pos (sub_pos.2 hxa)
            (add_pos_of_pos_of_nonneg ha hx.1)]
      let s : ℝ := Real.sqrt (a ^ 2 - x ^ 2)
      have hs : 0 < s := Real.sqrt_pos.2 hD
      have hs2 : s ^ 2 = a ^ 2 - x ^ 2 := by
        dsimp [s]
        exact Real.sq_sqrt hD.le
      calc
        (∫ y in (0 : ℝ)..b / a * Real.sqrt (a ^ 2 - x ^ 2),
            areaFactor a x y) =
            ∫ y in (0 : ℝ)..(b / a) * s,
              a / Real.sqrt (s ^ 2 - y ^ 2) := by
          apply intervalIntegral.integral_congr
          intro y hy
          dsimp [areaFactor, s]
          rw [Real.sq_sqrt hD.le]
        _ = a * (Real.arcsin (b / a) - Real.arcsin 0) :=
          scaled_slice_integral a s (b / a) hs hc0 hc1
        _ = a *
            (endpointPrimitive a x
                (b / a * Real.sqrt (a ^ 2 - x ^ 2)) -
              endpointPrimitive a x 0) := by
          dsimp [endpointPrimitive, s]
          field_simp [hs.ne']
          simp
  rw [gap9 a b ha hb hba]
  calc
    8 *
          (∫ x in (0 : ℝ)..a,
            ∫ y in (0 : ℝ)..b / a * Real.sqrt (a ^ 2 - x ^ 2),
              areaFactor a x y) =
        8 *
          ∫ x in (0 : ℝ)..a,
            a *
              (endpointPrimitive a x
                  (b / a * Real.sqrt (a ^ 2 - x ^ 2)) -
                endpointPrimitive a x 0) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x hx
      exact hinner x hx
    _ = 8 * a *
        ∫ x in (0 : ℝ)..a,
          endpointPrimitive a x
              (b / a * Real.sqrt (a ^ 2 - x ^ 2)) -
            endpointPrimitive a x 0 := by
      rw [intervalIntegral.integral_const_mul]
      ring

theorem gap11 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    8 * a *
        (∫ x in (0 : ℝ)..a,
          endpointPrimitive a x
              (b / a * Real.sqrt (a ^ 2 - x ^ 2)) -
            endpointPrimitive a x 0) =
      8 * a ^ 2 * Real.arcsin (b / a) := by
  have hconst :
      (∫ x in (0 : ℝ)..a,
          endpointPrimitive a x
              (b / a * Real.sqrt (a ^ 2 - x ^ 2)) -
            endpointPrimitive a x 0) =
        ∫ x in (0 : ℝ)..a, Real.arcsin (b / a) := by
    refine intervalIntegral.integral_congr_ae' ?_ ?_
    · filter_upwards [ae_real_ne a] with x hxa_ne
      intro hx
      have hxa : x < a := lt_of_le_of_ne hx.2 hxa_ne
      have hD : 0 < a ^ 2 - x ^ 2 := by
        nlinarith
          [mul_pos (sub_pos.2 hxa)
            (add_pos ha hx.1)]
      have hs :
          Real.sqrt (a ^ 2 - x ^ 2) ≠ 0 :=
        (Real.sqrt_pos.2 hD).ne'
      dsimp [endpointPrimitive]
      field_simp [hs]
      simp
    · filter_upwards with x
      intro hx
      exfalso
      linarith [hx.1, hx.2]
  rw [hconst]
  simp
  ring

theorem gap12 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    surfaceArea a b = 8 * a ^ 2 * Real.arcsin (b / a) := by
  rw [gap10 a b ha hb hba, gap11 a b ha hb hba]

end

end ProofGap.Exercise4038
