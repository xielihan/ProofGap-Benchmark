import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2964

noncomputable section

open scoped Interval

def reduced (x : ℝ) : ℝ :=
  x - 3 * (Int.floor (x / 3) : ℝ)

def target (x : ℝ) : ℝ :=
  let r := reduced x
  if r ≤ 1 then r else if r < 2 then 1 else 3 - r

def coefficientIntegral (n : ℕ) : ℝ :=
  2 / 3 *
      (∫ x in 0..1,
        x * Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) +
    2 / 3 *
      (∫ x in 1..2,
        Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) +
    2 / 3 *
      (∫ x in 2..3,
        (3 - x) * Real.cos (2 * (n : ℝ) * Real.pi * x / 3))

def coefficientClosed (n : ℕ) : ℝ :=
  -3 / (((n : ℝ) * Real.pi) ^ 2) +
    3 / (((n : ℝ) * Real.pi) ^ 2) *
      (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * Real.pi / 3)

def rawSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    (-1 / (n : ℝ) ^ 2 +
        (-1 : ℝ) ^ n / (n : ℝ) ^ 2 *
          Real.cos ((n : ℝ) * Real.pi / 3)) *
      Real.cos (2 * (n : ℝ) * Real.pi * x / 3)

def baseCosineSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    1 / (n : ℝ) ^ 2 *
      Real.cos (2 * (n : ℝ) * Real.pi * x / 3)

def tripleCosineSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ,
    let n : ℕ := k + 1
    1 / (n : ℝ) ^ 2 * Real.cos (2 * (n : ℝ) * Real.pi * x)

def fourierSeries (x : ℝ) : ℝ :=
  2 / 3 -
    9 / (2 * Real.pi ^ 2) * baseCosineSeries x +
    1 / (2 * Real.pi ^ 2) * tripleCosineSeries x

private theorem reduced_add_three (x : ℝ) :
    reduced (x + 3) = reduced x := by
  unfold reduced
  rw [show (x + 3) / 3 = x / 3 + 1 by ring,
    Int.floor_add_one]
  push_cast
  ring

private theorem floor_div_three_eq_zero {x : ℝ}
    (hx0 : 0 ≤ x) (hx3 : x < 3) :
    Int.floor (x / 3) = 0 := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num <;> linarith

private theorem target_eq_left {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    target x = x := by
  have hfloor := floor_div_three_eq_zero hx0 (by linarith)
  simp only [target, reduced, hfloor, Int.cast_zero, mul_zero, sub_zero]
  split_ifs <;> linarith

private theorem target_eq_middle {x : ℝ}
    (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    target x = 1 := by
  have hfloor := floor_div_three_eq_zero (by linarith) (by linarith)
  simp only [target, reduced, hfloor, Int.cast_zero, mul_zero, sub_zero]
  split_ifs <;> linarith

private theorem target_eq_right {x : ℝ}
    (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    target x = 3 - x := by
  by_cases h : x = 3
  · subst x
    norm_num [target, reduced]
  · have hxlt : x < 3 := lt_of_le_of_ne hx3 h
    have hfloor := floor_div_three_eq_zero (by linarith) hxlt
    simp only [target, reduced, hfloor, Int.cast_zero, mul_zero, sub_zero]
    split_ifs <;> linarith

private theorem reduced_mem (x : ℝ) :
    0 ≤ reduced x ∧ reduced x < 3 := by
  have hle :
      (Int.floor (x / 3) : ℝ) ≤ x / 3 :=
    Int.floor_le (x / 3)
  have hlt :
      x / 3 < (Int.floor (x / 3) : ℝ) + 1 :=
    Int.lt_floor_add_one (x / 3)
  unfold reduced
  constructor <;> linarith

private theorem target_neg_eq (x : ℝ) :
    target (-x) = target x := by
  let z : ℤ := Int.floor (x / 3)
  let r : ℝ := reduced x
  have hrange : 0 ≤ r ∧ r < 3 := by
    exact reduced_mem x
  have hx : x = r + 3 * (z : ℝ) := by
    simp only [r, z, reduced]
    ring
  by_cases hr : r = 0
  · have hfloor : Int.floor ((-x) / 3) = -z := by
      rw [Int.floor_eq_iff]
      push_cast
      rw [hx, hr]
      constructor <;> linarith
    unfold target
    have hredneg : reduced (-x) = 0 := by
      unfold reduced
      rw [hfloor, hx, hr]
      push_cast
      ring
    rw [hredneg]
    change (if (0 : ℝ) ≤ 1 then 0 else
      if (0 : ℝ) < 2 then 1 else 3 - 0) =
      (if r ≤ 1 then r else if r < 2 then 1 else 3 - r)
    simp [hr]
  · have hrpos : 0 < r := lt_of_le_of_ne hrange.1 (Ne.symm hr)
    have hfloor : Int.floor ((-x) / 3) = -z - 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      rw [hx]
      constructor <;> linarith
    have hredneg : reduced (-x) = 3 - r := by
      unfold reduced
      rw [hfloor, hx]
      push_cast
      ring
    unfold target
    rw [hredneg]
    change
      (if 3 - r ≤ 1 then 3 - r else
        if 3 - r < 2 then 1 else 3 - (3 - r)) =
      (if r ≤ 1 then r else if r < 2 then 1 else 3 - r)
    split_ifs <;> linarith

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Function.Periodic f 3 := by
  intro x
  rw [hf, hf]
  unfold target
  rw [reduced_add_three]

theorem gap2 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    Function.Even f := by
  intro x
  rw [hf, hf, target_neg_eq]

theorem gap3 (s : ℕ → ℝ)
    (hs : ∀ n : ℕ, 1 ≤ n → s n = 0) :
    ∀ n : ℕ, 1 ≤ n → s n = 0 := by
  exact hs

theorem gap4 (f : ℝ → ℝ) (c : ℕ → ℝ)
    (hf : ∀ x, f x = target x)
    (hc : c 0 = 1 / (3 / 2 : ℝ) * ∫ x in 0..3, f x) :
    c 0 = 1 / (3 / 2 : ℝ) * ∫ x in 0..3, f x := by
  exact hc

theorem gap5 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    1 / (3 / 2 : ℝ) * (∫ x in 0..3, f x) =
      2 / 3 * (∫ x in 0..1, x) +
        2 / 3 * (∫ _x in 1..2, (1 : ℝ)) +
        2 / 3 * (∫ x in 2..3, 3 - x) := by
  have heq01 : Set.EqOn f (fun x : ℝ => x) (Set.uIcc 0 1) := by
    intro x hx
    rw [hf]
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact target_eq_left hx'.1 hx'.2
  have heq12 : Set.EqOn f (fun _x : ℝ => (1 : ℝ)) (Set.uIcc 1 2) := by
    intro x hx
    rw [hf]
    have hx' : x ∈ Set.Icc (1 : ℝ) 2 := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
    exact target_eq_middle hx'.1 hx'.2
  have heq23 : Set.EqOn f (fun x : ℝ => 3 - x) (Set.uIcc 2 3) := by
    intro x hx
    rw [hf]
    have hx' : x ∈ Set.Icc (2 : ℝ) 3 := by
      simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using hx
    exact target_eq_right hx'.1 hx'.2
  have hf01 : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_congr (heq01.mono Set.uIoc_subset_uIcc)]
    exact continuous_id.intervalIntegrable _ _
  have hf12 : IntervalIntegrable f MeasureTheory.volume 1 2 := by
    rw [intervalIntegrable_congr (heq12.mono Set.uIoc_subset_uIcc)]
    exact intervalIntegrable_const
  have hf23 : IntervalIntegrable f MeasureTheory.volume 2 3 := by
    rw [intervalIntegrable_congr (heq23.mono Set.uIoc_subset_uIcc)]
    exact (continuous_const.sub continuous_id).intervalIntegrable _ _
  have hf02 : IntervalIntegrable f MeasureTheory.volume 0 2 :=
    hf01.trans hf12
  rw [← intervalIntegral.integral_add_adjacent_intervals hf02 hf23,
    ← intervalIntegral.integral_add_adjacent_intervals hf01 hf12]
  have hi01 :
      (∫ x in (0 : ℝ)..1, f x) = ∫ x in (0 : ℝ)..1, x := by
    exact intervalIntegral.integral_congr heq01
  have hi12 :
      (∫ x in (1 : ℝ)..2, f x) = ∫ _x in (1 : ℝ)..2, (1 : ℝ) := by
    exact intervalIntegral.integral_congr heq12
  have hi23 :
      (∫ x in (2 : ℝ)..3, f x) = ∫ x in (2 : ℝ)..3, 3 - x := by
    exact intervalIntegral.integral_congr heq23
  rw [hi01, hi12, hi23]
  ring

theorem gap6 :
    2 / 3 * (∫ x in 0..1, x) +
        2 / 3 * (∫ _x in 1..2, (1 : ℝ)) +
        2 / 3 * (∫ x in 2..3, 3 - x) =
      4 / 3 := by
  have hsub :
      (∫ x in (2 : ℝ)..3, 3 - x) =
        (∫ _x in (2 : ℝ)..3, (3 : ℝ)) -
          ∫ x in (2 : ℝ)..3, x := by
    have hc : IntervalIntegrable (fun _ : ℝ => (3 : ℝ))
        MeasureTheory.volume 2 3 := intervalIntegrable_const
    have hx : IntervalIntegrable (fun x : ℝ => x)
        MeasureTheory.volume 2 3 :=
      continuous_id.intervalIntegrable _ _
    exact intervalIntegral.integral_sub hc hx
  rw [hsub]
  norm_num [integral_id,
    intervalIntegral.integral_const,
    intervalIntegral.integral_sub]

theorem gap7 (f : ℝ → ℝ) (c : ℕ → ℝ)
    (hf : ∀ x, f x = target x)
    (hc : c 0 = 1 / (3 / 2 : ℝ) * ∫ x in 0..3, f x) :
    c 0 = 4 / 3 := by
  rw [hc, gap5 f hf, gap6]

theorem gap8 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n := by
  exact hc

private theorem integral_affine_mul_cos
    (c d w a b : ℝ) (hw : w ≠ 0) :
    (∫ x in a..b, (c + d * x) * Real.cos (w * x)) =
      ((c + d * b) * Real.sin (w * b) / w +
          d * Real.cos (w * b) / w ^ 2) -
        ((c + d * a) * Real.sin (w * a) / w +
          d * Real.cos (w * a) / w ^ 2) := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt
        (fun y =>
          (c + d * y) * Real.sin (w * y) / w +
            d * Real.cos (w * y) / w ^ 2)
        ((c + d * x) * Real.cos (w * x)) x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => w * y) w x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul w
    have hs :
        HasDerivAt (fun y : ℝ => Real.sin (w * y))
          (Real.cos (w * x) * w) x := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sin (w * x)).comp x hinner
    have hcos :
        HasDerivAt (fun y : ℝ => Real.cos (w * y))
          (-Real.sin (w * x) * w) x := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_cos (w * x)).comp x hinner
    have hlin :
        HasDerivAt (fun y : ℝ => c + d * y) d x := by
      convert (hasDerivAt_const x c).add ((hasDerivAt_id x).const_mul d)
        using 1 <;> ring
    convert
      ((hlin.mul hs).div_const w).add
        ((hcos.const_mul d).div_const (w ^ 2)) using 1 <;>
      field_simp [hw] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    ((by
      fun_prop : Continuous
        (fun x : ℝ => (c + d * x) * Real.cos (w * x))).intervalIntegrable _ _)]

theorem gap9 (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, 1 ≤ n → c n = coefficientIntegral n) :
    ∀ n : ℕ, 1 ≤ n → c n = coefficientClosed n := by
  intro n hn
  rw [hc n hn]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  let w : ℝ := 2 * (n : ℝ) * Real.pi / 3
  have hw : w ≠ 0 := by
    dsimp [w]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn0)
      Real.pi_ne_zero) (by norm_num)
  have hi1 :
      (∫ x in (0 : ℝ)..1,
        x * Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) =
        ((0 + 1 * 1) * Real.sin (w * 1) / w +
            1 * Real.cos (w * 1) / w ^ 2) -
          ((0 + 1 * 0) * Real.sin (w * 0) / w +
            1 * Real.cos (w * 0) / w ^ 2) := by
    calc
      (∫ x in (0 : ℝ)..1,
          x * Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) =
          ∫ x in (0 : ℝ)..1,
            (0 + 1 * x) * Real.cos (w * x) := by
              apply intervalIntegral.integral_congr
              intro x _
              dsimp [w]
              congr 2 <;> ring
      _ = _ := integral_affine_mul_cos 0 1 w 0 1 hw
  have hi2 :
      (∫ x in (1 : ℝ)..2,
        Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) =
        ((1 + 0 * 2) * Real.sin (w * 2) / w +
            0 * Real.cos (w * 2) / w ^ 2) -
          ((1 + 0 * 1) * Real.sin (w * 1) / w +
            0 * Real.cos (w * 1) / w ^ 2) := by
    calc
      (∫ x in (1 : ℝ)..2,
          Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) =
          ∫ x in (1 : ℝ)..2,
            (1 + 0 * x) * Real.cos (w * x) := by
              apply intervalIntegral.integral_congr
              intro x _
              dsimp [w]
              congr 2 <;> ring
      _ = _ := integral_affine_mul_cos 1 0 w 1 2 hw
  have hi3 :
      (∫ x in (2 : ℝ)..3,
        (3 - x) * Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) =
        ((3 + (-1) * 3) * Real.sin (w * 3) / w +
            (-1) * Real.cos (w * 3) / w ^ 2) -
          ((3 + (-1) * 2) * Real.sin (w * 2) / w +
            (-1) * Real.cos (w * 2) / w ^ 2) := by
    calc
      (∫ x in (2 : ℝ)..3,
          (3 - x) * Real.cos (2 * (n : ℝ) * Real.pi * x / 3)) =
          ∫ x in (2 : ℝ)..3,
            (3 + (-1) * x) * Real.cos (w * x) := by
              apply intervalIntegral.integral_congr
              intro x _
              dsimp [w]
              congr 2 <;> ring
      _ = _ := integral_affine_mul_cos 3 (-1) w 2 3 hw
  have hcos3 : Real.cos (w * 3) = 1 := by
    rw [show w * 3 = (n : ℝ) * (2 * Real.pi) by
      dsimp [w]; ring, Real.cos_nat_mul_two_pi]
  have hcos2 : Real.cos (w * 2) = Real.cos w := by
    rw [show w * 2 = (n : ℝ) * (2 * Real.pi) - w by
      dsimp [w]; ring, Real.cos_nat_mul_two_pi_sub]
  have hcos1 :
      Real.cos w =
        (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * Real.pi / 3) := by
    rw [show w = (n : ℝ) * Real.pi -
        (n : ℝ) * Real.pi / 3 by dsimp [w]; ring,
      Real.cos_nat_mul_pi_sub]
  unfold coefficientIntegral coefficientClosed
  rw [hi1, hi2, hi3]
  norm_num
  rw [hcos3, hcos2, hcos1]
  dsimp [w]
  field_simp [hn0, Real.pi_ne_zero]
  ring

private theorem neg_one_pow_mul_cos (n : ℕ) :
    (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * Real.pi / 3) =
      if 3 ∣ n then 1 else -(1 / 2 : ℝ) := by
  have hprod :
      (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * Real.pi / 3) =
        Real.cos (2 * (n : ℝ) * Real.pi / 3) := by
    rw [show 2 * (n : ℝ) * Real.pi / 3 =
        (n : ℝ) * Real.pi - (n : ℝ) * Real.pi / 3 by ring,
      Real.cos_nat_mul_pi_sub]
  rw [hprod]
  have hdecomp :
      2 * (n : ℝ) * Real.pi / 3 =
        2 * (n % 3 : ℕ) * Real.pi / 3 +
          (n / 3 : ℕ) * (2 * Real.pi) := by
    have hn :
        ((n % 3 : ℕ) : ℝ) + 3 * ((n / 3 : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.mod_add_div n 3
    rw [← hn]
    ring
  rw [hdecomp, Real.cos_add_nat_mul_two_pi]
  have hrem : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  have htwo :
      Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have hfour :
      Real.cos (2 * (2 : ℕ) * Real.pi / 3) =
        -(1 / 2 : ℝ) := by
    calc
      Real.cos (2 * (2 : ℕ) * Real.pi / 3) =
          Real.cos (2 * Real.pi - 2 * Real.pi / 3) := by
            congr 1
            norm_num
            ring
      _ = Real.cos (2 * Real.pi / 3) := Real.cos_two_pi_sub _
      _ = -(1 / 2 : ℝ) := htwo
  interval_cases h : n % 3
  · simp [h, Nat.dvd_iff_mod_eq_zero]
  · simpa [h, Nat.dvd_iff_mod_eq_zero] using htwo
  · simpa [h, Nat.dvd_iff_mod_eq_zero] using hfour

private def baseTerm (x : ℝ) (k : ℕ) : ℝ :=
  1 / (k + 1 : ℝ) ^ 2 *
    Real.cos (2 * (k + 1 : ℝ) * Real.pi * x / 3)

private def tripleTerm (x : ℝ) (k : ℕ) : ℝ :=
  1 / (k + 1 : ℝ) ^ 2 *
    Real.cos (2 * (k + 1 : ℝ) * Real.pi * x)

private def sparseTerm (x : ℝ) (k : ℕ) : ℝ :=
  if 3 ∣ k + 1 then baseTerm x k else 0

private theorem summable_weight :
    Summable (fun k : ℕ => 1 / (k + 1 : ℝ) ^ 2) := by
  have h :
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr h

private theorem summable_cosTerm (angle : ℕ → ℝ) :
    Summable (fun k : ℕ =>
      1 / (k + 1 : ℝ) ^ 2 * Real.cos (angle k)) := by
  apply summable_weight.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul]
  have hnonneg : 0 ≤ 1 / (k + 1 : ℝ) ^ 2 := by positivity
  rw [abs_of_nonneg hnonneg]
  calc
    1 / (k + 1 : ℝ) ^ 2 * |Real.cos (angle k)| ≤
        1 / (k + 1 : ℝ) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hnonneg
    _ = 1 / (k + 1 : ℝ) ^ 2 := by ring

private theorem summable_baseTerm (x : ℝ) :
    Summable (baseTerm x) := by
  exact summable_cosTerm
    (fun k => 2 * (k + 1 : ℝ) * Real.pi * x / 3)

private theorem summable_tripleTerm (x : ℝ) :
    Summable (tripleTerm x) := by
  exact summable_cosTerm
    (fun k => 2 * (k + 1 : ℝ) * Real.pi * x)

private theorem hasSum_sparseTerm (x : ℝ) :
    HasSum (sparseTerm x)
      (1 / (3 : ℝ) ^ 2 * ∑' k : ℕ, tripleTerm x k) := by
  let g : ℕ → ℕ := fun m => 3 * m + 2
  have hg : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    omega
  have hoff : ∀ k ∉ Set.range g, sparseTerm x k = 0 := by
    intro k hk
    unfold sparseTerm
    rw [if_neg]
    intro hd
    obtain ⟨q, hq⟩ := hd
    apply hk
    refine ⟨q - 1, ?_⟩
    dsimp [g]
    omega
  have hcomp :
      HasSum (sparseTerm x ∘ g)
        (1 / (3 : ℝ) ^ 2 * ∑' k : ℕ, tripleTerm x k) := by
    have hs := (summable_tripleTerm x).hasSum.mul_left (1 / (3 : ℝ) ^ 2)
    refine hs.congr_fun ?_
    intro m
    simp only [Function.comp_apply]
    unfold sparseTerm baseTerm tripleTerm
    dsimp [g]
    rw [if_pos (by omega : 3 ∣ 3 * m + 2 + 1)]
    push_cast
    field_simp
    ring
  exact (hg.hasSum_iff hoff).mp hcomp

private theorem raw_term_eq (x : ℝ) (k : ℕ) :
    (-1 / (k + 1 : ℝ) ^ 2 +
          (-1 : ℝ) ^ (k + 1) / (k + 1 : ℝ) ^ 2 *
            Real.cos ((k + 1 : ℝ) * Real.pi / 3)) *
        Real.cos (2 * (k + 1 : ℝ) * Real.pi * x / 3) =
      -(3 / 2 : ℝ) * baseTerm x k +
        3 / 2 * sparseTerm x k := by
  have hsign := neg_one_pow_mul_cos (k + 1)
  norm_num only [Nat.cast_add, Nat.cast_one] at hsign
  rw [div_mul_eq_mul_div, hsign]
  unfold baseTerm sparseTerm
  by_cases hd : 3 ∣ k + 1
  · rw [if_pos hd, if_pos hd]
    unfold baseTerm
    ring
  · rw [if_neg hd, if_neg hd]
    ring

private theorem rawSeries_eq_decomposition :
    ∀ x,
      rawSeries x =
        -(3 / 2) * baseCosineSeries x +
          3 / 2 * (1 / (3 : ℝ) ^ 2) * tripleCosineSeries x := by
  intro x
  unfold rawSeries baseCosineSeries tripleCosineSeries
  rw [tsum_congr (fun k => by
    simpa only [Nat.cast_add, Nat.cast_one] using raw_term_eq x k)]
  have hb := (summable_baseTerm x).mul_left (-(3 / 2 : ℝ))
  have hs := (hasSum_sparseTerm x).summable.mul_left (3 / 2)
  rw [hb.tsum_add hs]
  rw [tsum_mul_left, tsum_mul_left, (hasSum_sparseTerm x).tsum_eq]
  simp only [baseTerm, tripleTerm, Nat.cast_add, Nat.cast_one]
  ring

private theorem hasSum_cosine_sq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (fun n : ℕ =>
        1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * t))
      (Real.pi ^ 2 * (t ^ 2 - t + 1 / 6)) := by
  have h :=
    hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num) ht
  change
    HasSum
      (fun n : ℕ =>
        1 / (n : ℝ) ^ (2 * 1) * Real.cos (2 * Real.pi * n * t))
      ((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 /
        Nat.factorial (2 * 1) * bernoulliFun (2 * 1) t) at h
  rw [bernoulliFun_two] at h
  norm_num [div_eq_mul_inv] at h
  convert h using 1
  · funext n
    congr 2 <;> ring
  · ring

private theorem hasSum_cosine_sq_shifted {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum
      (fun k : ℕ =>
        1 / ((k + 1 : ℕ) : ℝ) ^ 2 *
          Real.cos (2 * ((k + 1 : ℕ) : ℝ) * Real.pi * t))
      (Real.pi ^ 2 * (t ^ 2 - t + 1 / 6)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_cosine_sq ht)
  convert h using 1
  · funext k
    norm_num only [Nat.cast_add, Nat.cast_one]
    congr 2 <;> ring
  · norm_num

private theorem baseCosineSeries_eq (x : ℝ)
    (hx0 : 0 ≤ x) (hx3 : x ≤ 3) :
    baseCosineSeries x =
      Real.pi ^ 2 * ((x / 3) ^ 2 - x / 3 + 1 / 6) := by
  have ht : x / 3 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hs := hasSum_cosine_sq_shifted ht
  rw [← hs.tsum_eq]
  unfold baseCosineSeries
  apply tsum_congr
  intro k
  dsimp only
  congr 2 <;> ring

private theorem tripleCosineSeries_eq_sub_nat (x : ℝ) (m : ℕ)
    (ht : x - m ∈ Set.Icc (0 : ℝ) 1) :
    tripleCosineSeries x =
      Real.pi ^ 2 * ((x - m) ^ 2 - (x - m) + 1 / 6) := by
  have hs := hasSum_cosine_sq_shifted ht
  rw [← hs.tsum_eq]
  unfold tripleCosineSeries
  apply tsum_congr
  intro k
  dsimp only
  congr 1
  rw [show
      2 * ((k + 1 : ℕ) : ℝ) * Real.pi * x =
        2 * ((k + 1 : ℕ) : ℝ) * Real.pi * (x - m) +
          ((k + 1) * m : ℕ) * (2 * Real.pi) by
        push_cast
        ring,
    Real.cos_add_nat_mul_two_pi]

theorem gap10 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    ∀ x, 0 ≤ x → x ≤ 3 →
      f x = 2 / 3 + 3 / Real.pi ^ 2 * rawSeries x := by
  intro x hx0 hx3
  rw [hf, rawSeries_eq_decomposition x,
    baseCosineSeries_eq x hx0 hx3]
  by_cases hx1 : x ≤ 1
  · have ht : x - (0 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
      simpa using And.intro hx0 hx1
    rw [target_eq_left hx0 hx1,
      tripleCosineSeries_eq_sub_nat x 0 ht]
    norm_num
    field_simp [Real.pi_ne_zero]
    ring
  · have hx1' : 1 ≤ x := by linarith
    by_cases hx2 : x ≤ 2
    · have ht : x - (1 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> norm_num <;> linarith
      rw [target_eq_middle hx1' hx2,
        tripleCosineSeries_eq_sub_nat x 1 ht]
      norm_num
      field_simp [Real.pi_ne_zero]
      ring
    · have hx2' : 2 ≤ x := by linarith
      have ht : x - (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> norm_num <;> linarith
      rw [target_eq_right hx2' hx3,
        tripleCosineSeries_eq_sub_nat x 2 ht]
      norm_num
      field_simp [Real.pi_ne_zero]
      ring

theorem gap11 :
    ∀ x,
      rawSeries x =
        -(3 / 2) * baseCosineSeries x +
          3 / 2 * (1 / (3 : ℝ) ^ 2) * tripleCosineSeries x := by
  exact rawSeries_eq_decomposition

theorem gap12 (f : ℝ → ℝ) (hf : ∀ x, f x = target x) :
    ∀ x, 0 ≤ x → x ≤ 3 →
      f x = fourierSeries x := by
  intro x hx0 hx3
  rw [gap10 f hf x hx0 hx3, gap11 x]
  unfold fourierSeries
  field_simp [Real.pi_ne_zero]
  ring

end

end ProofGap.Exercise2964
