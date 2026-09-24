import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3228_2

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.arccos (Real.sqrt (x / y))

def positiveClosure (x y : ℝ) : Prop :=
  0 < x ∧ x ≤ y

def positiveBranch (x y : ℝ) : Prop :=
  0 < x ∧ x < y

def negativeClosure (x y : ℝ) : Prop :=
  y ≤ x ∧ x < 0

def negativeBranch (x y : ℝ) : Prop :=
  y < x ∧ x < 0

def admissible (x y : ℝ) : Prop :=
  positiveBranch x y ∨ negativeBranch x y

def threeHalves (t : ℝ) : ℝ :=
  Real.rpow t (3 / 2 : ℝ)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def mixedYX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f t y) x

private theorem threeHalves_eq_mul_sqrt {t : ℝ} (ht : 0 < t) :
    threeHalves t = t * Real.sqrt t := by
  unfold threeHalves
  calc
    Real.rpow t (3 / 2 : ℝ) = Real.rpow t (1 + 1 / 2 : ℝ) := by norm_num
    _ = Real.rpow t 1 * Real.rpow t (1 / 2 : ℝ) :=
      Real.rpow_add ht 1 (1 / 2)
    _ = t * Real.sqrt t := by
      rw [show Real.rpow t 1 = t from Real.rpow_one t]
      rw [Real.sqrt_eq_rpow]
      change t * Real.rpow t (1 / 2 : ℝ) =
        t * Real.rpow t (1 / 2 : ℝ)
      rfl

private theorem sqrt_sq_mul (a b : ℝ) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 * b) = |a| * Real.sqrt b := by
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem gap1 :
    ∀ x y : ℝ, positiveClosure x y →
      u x y = Real.arccos (Real.sqrt (x / y)) := by
  intro x y h
  rfl

theorem gap2 :
    ∀ x y : ℝ, positiveClosure x y →
      Real.arccos (Real.sqrt (x / y)) =
        Real.arccos (Real.sqrt x / Real.sqrt y) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  rw [Real.sqrt_div (le_of_lt hx)]

theorem gap3 :
    ∀ x y : ℝ, positiveClosure x y →
      u x y = Real.arccos (Real.sqrt x / Real.sqrt y) := by
  intro x y h
  exact (gap1 x y h).trans (gap2 x y h)

theorem gap4 :
    ∀ x y : ℝ, positiveBranch x y →
      partialX u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          (1 / (2 * Real.sqrt x * Real.sqrt y)) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  have hy : 0 < y := lt_trans hx hxy
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  have hz0 : 0 < x / y := div_pos hx hy
  have hz1 : x / y < 1 := (div_lt_iff₀ hy).2 (by simpa using hxy)
  have hzsq : (Real.sqrt x / Real.sqrt y) ^ 2 = x / y := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hx), Real.sq_sqrt (le_of_lt hy)]
  have hznonneg : 0 ≤ Real.sqrt x / Real.sqrt y :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hzm : Real.sqrt x / Real.sqrt y ≠ -1 := by nlinarith
  have hzo : Real.sqrt x / Real.sqrt y ≠ 1 := by nlinarith [hzsq]
  have hs := (Real.hasDerivAt_sqrt hx.ne').div_const (Real.sqrt y)
  have ha := (Real.hasDerivAt_arccos hzm hzo).comp x hs
  have hd : HasDerivAt
      (fun t : ℝ => Real.arccos (Real.sqrt t / Real.sqrt y))
      (-(1 / Real.sqrt (1 - x / y)) *
        (1 / (2 * Real.sqrt x * Real.sqrt y))) x := by
    convert ha using 1
    rw [hzsq]
    ring
  have heq :
      (fun t : ℝ => u t y) =ᶠ[nhds x]
        (fun t : ℝ => Real.arccos (Real.sqrt t / Real.sqrt y)) := by
    filter_upwards [Ioo_mem_nhds hx hxy] with t ht
    exact gap3 t y ⟨ht.1, le_of_lt ht.2⟩
  change deriv (fun t : ℝ => u t y) x = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap5 :
    ∀ x y : ℝ, positiveBranch x y →
      -(1 / Real.sqrt (1 - x / y)) *
          (1 / (2 * Real.sqrt x * Real.sqrt y)) =
        -(1 / (2 * Real.sqrt (x * (y - x)))) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  have hy : 0 < y := lt_trans hx hxy
  have hd : 0 < y - x := sub_pos.2 hxy
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  have hsd : Real.sqrt (y - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  rw [show 1 - x / y = (y - x) / y by field_simp]
  rw [Real.sqrt_div (le_of_lt hd)]
  rw [Real.sqrt_mul (le_of_lt hx)]
  field_simp

theorem gap6 :
    ∀ x y : ℝ, positiveBranch x y →
      partialX u x y = -(1 / (2 * Real.sqrt (x * (y - x)))) := by
  intro x y h
  calc
    partialX u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          (1 / (2 * Real.sqrt x * Real.sqrt y)) := gap4 x y h
    _ = -(1 / (2 * Real.sqrt (x * (y - x)))) := gap5 x y h

theorem gap7 :
    ∀ x y : ℝ, positiveBranch x y →
      partialY u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          -(Real.sqrt x / (2 * threeHalves y)) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  have hy : 0 < y := lt_trans hx hxy
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  have hz0 : 0 < x / y := div_pos hx hy
  have hz1 : x / y < 1 := (div_lt_iff₀ hy).2 (by simpa using hxy)
  have hzsq : (Real.sqrt x / Real.sqrt y) ^ 2 = x / y := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hx), Real.sq_sqrt (le_of_lt hy)]
  have hznonneg : 0 ≤ Real.sqrt x / Real.sqrt y :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hzm : Real.sqrt x / Real.sqrt y ≠ -1 := by nlinarith
  have hzo : Real.sqrt x / Real.sqrt y ≠ 1 := by nlinarith [hzsq]
  have hs := Real.hasDerivAt_sqrt hy.ne'
  have hq := (hasDerivAt_const (x := y) (Real.sqrt x)).div hs hsy
  have ha := (Real.hasDerivAt_arccos hzm hzo).comp y hq
  have hd : HasDerivAt
      (fun t : ℝ => Real.arccos (Real.sqrt x / Real.sqrt t))
      (-(1 / Real.sqrt (1 - x / y)) *
        -(Real.sqrt x / (2 * threeHalves y))) y := by
    convert ha using 1
    rw [hzsq, threeHalves_eq_mul_sqrt hy]
    simp only [Function.comp_apply, zero_mul, mul_zero, zero_sub,
      zero_add, add_zero, one_mul, mul_one]
    rw [Real.sq_sqrt (le_of_lt hy)]
    field_simp [hsy] <;> ring
  have heq :
      (fun t : ℝ => u x t) =ᶠ[nhds y]
        (fun t : ℝ => Real.arccos (Real.sqrt x / Real.sqrt t)) := by
    filter_upwards [Ioo_mem_nhds hxy (by linarith : y < y + 1)] with t ht
    exact gap3 x t ⟨hx, le_of_lt ht.1⟩
  change deriv (fun t : ℝ => u x t) y = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap8 :
    ∀ x y : ℝ, positiveBranch x y →
      -(1 / Real.sqrt (1 - x / y)) *
          -(Real.sqrt x / (2 * threeHalves y)) =
        Real.sqrt x / (2 * Real.sqrt (y ^ 2 * (y - x))) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  have hy : 0 < y := lt_trans hx hxy
  have hd : 0 < y - x := sub_pos.2 hxy
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  have hsd : Real.sqrt (y - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  rw [show 1 - x / y = (y - x) / y by field_simp]
  rw [Real.sqrt_div (le_of_lt hd), threeHalves_eq_mul_sqrt hy]
  rw [sqrt_sq_mul y (y - x) (le_of_lt hd), abs_of_pos hy]
  field_simp

theorem gap9 :
    ∀ x y : ℝ, positiveBranch x y →
      partialY u x y =
        Real.sqrt x / (2 * Real.sqrt (y ^ 2 * (y - x))) := by
  intro x y h
  calc
    partialY u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          -(Real.sqrt x / (2 * threeHalves y)) := gap7 x y h
    _ = Real.sqrt x / (2 * Real.sqrt (y ^ 2 * (y - x))) := gap8 x y h

theorem gap10 :
    ∀ x y : ℝ, positiveBranch x y →
      mixedXY u x y =
        1 / (4 * Real.sqrt x * threeHalves (y - x)) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  have hdif : 0 < y - x := sub_pos.2 hxy
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsd : Real.sqrt (y - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdif)
  have hl : HasDerivAt (fun t : ℝ => t - x) 1 y :=
    (hasDerivAt_id y).sub_const x
  have hs := (Real.hasDerivAt_sqrt hdif.ne').comp y hl
  have hden := (hasDerivAt_const (x := y) (2 * Real.sqrt x)).mul hs
  have hraw := ((hasDerivAt_const (x := y) (1 : ℝ)).div hden
    (mul_ne_zero (mul_ne_zero (by norm_num) hsx) hsd)).neg
  have hd : HasDerivAt
      (fun t : ℝ => -(1 / (2 * Real.sqrt x * Real.sqrt (t - x))))
      (1 / (4 * Real.sqrt x * threeHalves (y - x))) y := by
    convert hraw using 1
    rw [threeHalves_eq_mul_sqrt hdif]
    simp only [Function.comp_apply, Pi.mul_apply, zero_mul, mul_zero,
      zero_add, add_zero, zero_sub, one_mul, mul_one]
    field_simp [hsx, hsd] <;>
      ring_nf <;>
      simp only [Real.sq_sqrt (le_of_lt hx),
        Real.sq_sqrt (le_of_lt hdif)] <;>
      ring
  have heq :
      (fun t : ℝ => partialX u x t) =ᶠ[nhds y]
        (fun t : ℝ => -(1 / (2 * Real.sqrt x * Real.sqrt (t - x)))) := by
    filter_upwards [Ioo_mem_nhds hxy (by linarith : y < y + 1)] with t ht
    calc
      partialX u x t = -(1 / (2 * Real.sqrt (x * (t - x)))) :=
        gap6 x t ⟨hx, ht.1⟩
      _ = -(1 / (2 * Real.sqrt x * Real.sqrt (t - x))) := by
        rw [Real.sqrt_mul (le_of_lt hx)]
        ring
  change deriv (fun t : ℝ => partialX u x t) y = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap11 :
    ∀ x y : ℝ, positiveBranch x y →
      mixedYX u x y =
        1 / (4 * Real.sqrt x * Real.sqrt (y ^ 2 * (y - x))) +
          Real.sqrt x / (4 * y * threeHalves (y - x)) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  have hy : 0 < y := lt_trans hx hxy
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hdif : 0 < y - x := sub_pos.2 hxy
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsd : Real.sqrt (y - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdif)
  have hsn := Real.hasDerivAt_sqrt hx.ne'
  have hl : HasDerivAt (fun t : ℝ => y - t) (-1) x := by
    simpa using (hasDerivAt_const (x := x) y).sub (hasDerivAt_id x)
  have hss := (Real.hasDerivAt_sqrt hdif.ne').comp x hl
  have hden := (hasDerivAt_const (x := x) (2 * y)).mul hss
  have hraw := hsn.div hden
    (mul_ne_zero (mul_ne_zero (by norm_num) hy0) hsd)
  have hd : HasDerivAt
      (fun t : ℝ => Real.sqrt t / (2 * y * Real.sqrt (y - t)))
      (1 / (4 * Real.sqrt x * Real.sqrt (y ^ 2 * (y - x))) +
        Real.sqrt x / (4 * y * threeHalves (y - x))) x := by
    convert hraw using 1
    rw [sqrt_sq_mul y (y - x) (le_of_lt hdif), abs_of_pos hy,
      threeHalves_eq_mul_sqrt hdif]
    simp only [Function.comp_apply, Pi.mul_apply, zero_mul, mul_zero,
      zero_add, add_zero, zero_sub, one_mul, mul_one]
    field_simp [hsx, hsd, hy0] <;>
      ring_nf <;>
      simp only [Real.sq_sqrt (le_of_lt hx),
        Real.sq_sqrt (le_of_lt hdif)] <;>
      ring
  have heq :
      (fun t : ℝ => partialY u t y) =ᶠ[nhds x]
        (fun t : ℝ => Real.sqrt t / (2 * y * Real.sqrt (y - t))) := by
    filter_upwards [Ioo_mem_nhds hx hxy] with t ht
    calc
      partialY u t y = Real.sqrt t / (2 * Real.sqrt (y ^ 2 * (y - t))) :=
        gap9 t y ⟨ht.1, ht.2⟩
      _ = Real.sqrt t / (2 * y * Real.sqrt (y - t)) := by
        rw [sqrt_sq_mul y (y - t) (sub_nonneg.2 (le_of_lt ht.2)),
          abs_of_pos hy]
        ring
  change deriv (fun t : ℝ => partialY u t y) x = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap12 :
    ∀ x y : ℝ, positiveBranch x y →
      1 / (4 * Real.sqrt x * Real.sqrt (y ^ 2 * (y - x))) +
          Real.sqrt x / (4 * y * threeHalves (y - x)) =
        1 / (4 * Real.sqrt x * threeHalves (y - x)) := by
  intro x y h
  rcases h with ⟨hx, hxy⟩
  have hy : 0 < y := lt_trans hx hxy
  have hd : 0 < y - x := sub_pos.2 hxy
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsd : Real.sqrt (y - x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  rw [sqrt_sq_mul y (y - x) (le_of_lt hd), abs_of_pos hy,
    threeHalves_eq_mul_sqrt hd]
  field_simp
  nlinarith [Real.sq_sqrt (le_of_lt hx)]

theorem gap13 :
    ∀ x y : ℝ, positiveBranch x y →
      mixedYX u x y =
        1 / (4 * Real.sqrt x * threeHalves (y - x)) := by
  intro x y h
  exact (gap11 x y h).trans (gap12 x y h)

theorem gap14 :
    ∀ x y : ℝ, positiveBranch x y →
      mixedXY u x y = mixedYX u x y := by
  intro x y h
  rw [gap10 x y h, gap13 x y h]

theorem gap15 :
    ∀ y x : ℝ, negativeClosure x y →
      u x y =
        Real.arccos (Real.sqrt (-x) / Real.sqrt (-y)) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hy : y < 0 := lt_of_le_of_lt hyx hx
  unfold u
  rw [show x / y = (-x) / (-y) by ring]
  rw [Real.sqrt_div (by linarith : 0 ≤ -x)]

theorem gap16 :
    ∀ y x : ℝ, negativeBranch x y →
      partialX u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          -(1 / (2 * Real.sqrt (-x) * Real.sqrt (-y))) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hy : y < 0 := lt_trans hyx hx
  have hnx : 0 < -x := by linarith
  have hny : 0 < -y := by linarith
  have hsx : Real.sqrt (-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnx)
  have hsy : Real.sqrt (-y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hny)
  have hz0 : 0 < x / y := div_pos_of_neg_of_neg hx hy
  have hz1 : x / y < 1 := (div_lt_iff_of_neg hy).2 (by simpa using hyx)
  have hzsq : (Real.sqrt (-x) / Real.sqrt (-y)) ^ 2 = x / y := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hnx), Real.sq_sqrt (le_of_lt hny)]
    ring
  have hznonneg : 0 ≤ Real.sqrt (-x) / Real.sqrt (-y) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hzm : Real.sqrt (-x) / Real.sqrt (-y) ≠ -1 := by nlinarith
  have hzo : Real.sqrt (-x) / Real.sqrt (-y) ≠ 1 := by nlinarith [hzsq]
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hs := (Real.hasDerivAt_sqrt hnx.ne').comp x hneg
  have hq := hs.div_const (Real.sqrt (-y))
  have ha := (Real.hasDerivAt_arccos hzm hzo).comp x hq
  have hd : HasDerivAt
      (fun t : ℝ => Real.arccos (Real.sqrt (-t) / Real.sqrt (-y)))
      (-(1 / Real.sqrt (1 - x / y)) *
        -(1 / (2 * Real.sqrt (-x) * Real.sqrt (-y)))) x := by
    convert ha using 1
    rw [hzsq]
    ring
  have heq :
      (fun t : ℝ => u t y) =ᶠ[nhds x]
        (fun t : ℝ => Real.arccos (Real.sqrt (-t) / Real.sqrt (-y))) := by
    filter_upwards [Ioo_mem_nhds hyx hx] with t ht
    exact gap15 y t ⟨le_of_lt ht.1, ht.2⟩
  change deriv (fun t : ℝ => u t y) x = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap17 :
    ∀ y x : ℝ, negativeBranch x y →
      -(1 / Real.sqrt (1 - x / y)) *
          -(1 / (2 * Real.sqrt (-x) * Real.sqrt (-y))) =
        1 / (2 * Real.sqrt (-x) * Real.sqrt (x - y)) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hy : y < 0 := lt_trans hyx hx
  have hy0 : y ≠ 0 := ne_of_lt hy
  have hnx : 0 < -x := by linarith
  have hny : 0 < -y := by linarith
  have hd : 0 < x - y := sub_pos.2 hyx
  have hsx : Real.sqrt (-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnx)
  have hsy : Real.sqrt (-y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hny)
  have hsd : Real.sqrt (x - y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hratio : 1 - x / y = (x - y) / (-y) := by
    field_simp [hy0]
    ring
  rw [hratio]
  rw [Real.sqrt_div (le_of_lt hd)]
  field_simp [hsx, hsy, hsd] <;> ring

theorem gap18 :
    ∀ y x : ℝ, negativeBranch x y →
      partialX u x y =
        1 / (2 * Real.sqrt (-x) * Real.sqrt (x - y)) := by
  intro y x h
  calc
    partialX u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          -(1 / (2 * Real.sqrt (-x) * Real.sqrt (-y))) := gap16 y x h
    _ = 1 / (2 * Real.sqrt (-x) * Real.sqrt (x - y)) := gap17 y x h

theorem gap19 :
    ∀ y x : ℝ, negativeBranch x y →
      partialY u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          (Real.sqrt (-x) / (2 * threeHalves (-y))) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hy : y < 0 := lt_trans hyx hx
  have hy0 : y ≠ 0 := ne_of_lt hy
  have hnx : 0 < -x := by linarith
  have hny : 0 < -y := by linarith
  have hsx : Real.sqrt (-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnx)
  have hsy : Real.sqrt (-y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hny)
  have hz0 : 0 < x / y := div_pos_of_neg_of_neg hx hy
  have hz1 : x / y < 1 := (div_lt_iff_of_neg hy).2 (by simpa using hyx)
  have hzsq : (Real.sqrt (-x) / Real.sqrt (-y)) ^ 2 = x / y := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hnx), Real.sq_sqrt (le_of_lt hny)]
    ring
  have hznonneg : 0 ≤ Real.sqrt (-x) / Real.sqrt (-y) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hzm : Real.sqrt (-x) / Real.sqrt (-y) ≠ -1 := by nlinarith
  have hzo : Real.sqrt (-x) / Real.sqrt (-y) ≠ 1 := by nlinarith [hzsq]
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) y := by
    simpa using (hasDerivAt_id y).neg
  have hs := (Real.hasDerivAt_sqrt hny.ne').comp y hneg
  have hq := (hasDerivAt_const (x := y) (Real.sqrt (-x))).div hs hsy
  have ha := (Real.hasDerivAt_arccos hzm hzo).comp y hq
  have hd : HasDerivAt
      (fun t : ℝ => Real.arccos (Real.sqrt (-x) / Real.sqrt (-t)))
      (-(1 / Real.sqrt (1 - x / y)) *
        (Real.sqrt (-x) / (2 * threeHalves (-y)))) y := by
    convert ha using 1
    rw [hzsq, threeHalves_eq_mul_sqrt hny]
    simp only [Function.comp_apply, zero_mul, mul_zero, zero_sub,
      zero_add, add_zero, one_mul, mul_one]
    rw [Real.sq_sqrt (le_of_lt hny)]
    field_simp [hsy] <;> ring
  have heq :
      (fun t : ℝ => u x t) =ᶠ[nhds y]
        (fun t : ℝ => Real.arccos (Real.sqrt (-x) / Real.sqrt (-t))) := by
    filter_upwards [Ioo_mem_nhds (by linarith : y - 1 < y) hyx] with t ht
    exact gap15 t x ⟨le_of_lt ht.2, hx⟩
  change deriv (fun t : ℝ => u x t) y = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap20 :
    ∀ y x : ℝ, negativeBranch x y →
      -(1 / Real.sqrt (1 - x / y)) *
          (Real.sqrt (-x) / (2 * threeHalves (-y))) =
        -(Real.sqrt (-x) / (2 * Real.sqrt (x * y ^ 2 - y ^ 3))) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hy : y < 0 := lt_trans hyx hx
  have hy0 : y ≠ 0 := ne_of_lt hy
  have hnx : 0 < -x := by linarith
  have hny : 0 < -y := by linarith
  have hd : 0 < x - y := sub_pos.2 hyx
  have hsy : Real.sqrt (-y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hny)
  have hsd : Real.sqrt (x - y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hratio : 1 - x / y = (x - y) / (-y) := by
    field_simp [hy0]
    ring
  rw [hratio]
  rw [Real.sqrt_div (le_of_lt hd), threeHalves_eq_mul_sqrt hny]
  rw [show x * y ^ 2 - y ^ 3 = y ^ 2 * (x - y) by ring]
  rw [sqrt_sq_mul y (x - y) (le_of_lt hd), abs_of_neg hy]
  field_simp [hy0, hsy, hsd] <;> ring

theorem gap21 :
    ∀ y x : ℝ, negativeBranch x y →
      partialY u x y =
        -(Real.sqrt (-x) / (2 * Real.sqrt (x * y ^ 2 - y ^ 3))) := by
  intro y x h
  calc
    partialY u x y =
        -(1 / Real.sqrt (1 - x / y)) *
          (Real.sqrt (-x) / (2 * threeHalves (-y))) := gap19 y x h
    _ = -(Real.sqrt (-x) / (2 * Real.sqrt (x * y ^ 2 - y ^ 3))) := gap20 y x h

theorem gap22 :
    ∀ y x : ℝ, negativeBranch x y →
      mixedXY u x y =
        1 / (4 * Real.sqrt (-x) * threeHalves (x - y)) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hnx : 0 < -x := by linarith
  have hdif : 0 < x - y := sub_pos.2 hyx
  have hsx : Real.sqrt (-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnx)
  have hsd : Real.sqrt (x - y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdif)
  have hl : HasDerivAt (fun t : ℝ => x - t) (-1) y := by
    simpa using (hasDerivAt_const (x := y) x).sub (hasDerivAt_id y)
  have hs := (Real.hasDerivAt_sqrt hdif.ne').comp y hl
  have hden := (hasDerivAt_const (x := y) (2 * Real.sqrt (-x))).mul hs
  have hraw := (hasDerivAt_const (x := y) (1 : ℝ)).div hden
    (mul_ne_zero (mul_ne_zero (by norm_num) hsx) hsd)
  have hd : HasDerivAt
      (fun t : ℝ => 1 / (2 * Real.sqrt (-x) * Real.sqrt (x - t)))
      (1 / (4 * Real.sqrt (-x) * threeHalves (x - y))) y := by
    convert hraw using 1
    rw [threeHalves_eq_mul_sqrt hdif]
    simp only [Function.comp_apply, Pi.mul_apply, zero_mul, mul_zero,
      zero_add, add_zero, zero_sub, one_mul, mul_one]
    field_simp [hsx, hsd] <;>
      ring_nf <;>
      simp only [Real.sq_sqrt (le_of_lt hnx),
        Real.sq_sqrt (le_of_lt hdif)] <;>
      ring
  have heq :
      (fun t : ℝ => partialX u x t) =ᶠ[nhds y]
        (fun t : ℝ => 1 / (2 * Real.sqrt (-x) * Real.sqrt (x - t))) := by
    filter_upwards [Ioo_mem_nhds (by linarith : y - 1 < y) hyx] with t ht
    exact gap18 t x ⟨ht.2, hx⟩
  change deriv (fun t : ℝ => partialX u x t) y = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap23 :
    ∀ y x : ℝ, negativeBranch x y →
      mixedYX u x y =
        1 / (4 * Real.sqrt (-x) * Real.sqrt (x * y ^ 2 - y ^ 3)) +
          Real.sqrt (-x) /
            (4 * Real.sqrt (y ^ 2) * threeHalves (x - y)) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hy : y < 0 := lt_trans hyx hx
  have hy0 : y ≠ 0 := ne_of_lt hy
  have hnx : 0 < -x := by linarith
  have hdif : 0 < x - y := sub_pos.2 hyx
  have hsx : Real.sqrt (-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnx)
  have hsd : Real.sqrt (x - y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdif)
  have hnlin : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hsn := (Real.hasDerivAt_sqrt hnx.ne').comp x hnlin
  have hl : HasDerivAt (fun t : ℝ => t - y) 1 x :=
    (hasDerivAt_id x).sub_const y
  have hss := (Real.hasDerivAt_sqrt hdif.ne').comp x hl
  have hden := (hasDerivAt_const (x := x) (2 * (-y))).mul hss
  have hraw := (hsn.div hden
    (mul_ne_zero (mul_ne_zero (by norm_num) (neg_ne_zero.2 hy0)) hsd)).neg
  have hd : HasDerivAt
      (fun t : ℝ => -(Real.sqrt (-t) / (2 * (-y) * Real.sqrt (t - y))))
      (1 / (4 * Real.sqrt (-x) * Real.sqrt (x * y ^ 2 - y ^ 3)) +
        Real.sqrt (-x) /
          (4 * Real.sqrt (y ^ 2) * threeHalves (x - y))) x := by
    convert hraw using 1
    rw [show x * y ^ 2 - y ^ 3 = y ^ 2 * (x - y) by ring]
    rw [sqrt_sq_mul y (x - y) (le_of_lt hdif), Real.sqrt_sq_eq_abs,
      abs_of_neg hy, threeHalves_eq_mul_sqrt hdif]
    simp only [Function.comp_apply, Pi.mul_apply, zero_mul, mul_zero,
      zero_add, add_zero, zero_sub, one_mul, mul_one]
    field_simp [hsx, hsd, hy0] <;>
      ring_nf <;>
      simp only [Real.sq_sqrt (le_of_lt hnx),
        Real.sq_sqrt (le_of_lt hdif)] <;>
      ring
  have heq :
      (fun t : ℝ => partialY u t y) =ᶠ[nhds x]
        (fun t : ℝ => -(Real.sqrt (-t) / (2 * (-y) * Real.sqrt (t - y)))) := by
    filter_upwards [Ioo_mem_nhds hyx hx] with t ht
    calc
      partialY u t y =
          -(Real.sqrt (-t) / (2 * Real.sqrt (t * y ^ 2 - y ^ 3))) :=
        gap21 y t ⟨ht.1, ht.2⟩
      _ = -(Real.sqrt (-t) / (2 * (-y) * Real.sqrt (t - y))) := by
        rw [show t * y ^ 2 - y ^ 3 = y ^ 2 * (t - y) by ring]
        rw [sqrt_sq_mul y (t - y) (sub_nonneg.2 (le_of_lt ht.1)),
          abs_of_neg hy]
        ring
  change deriv (fun t : ℝ => partialY u t y) x = _
  exact (hd.congr_of_eventuallyEq heq).deriv

theorem gap24 :
    ∀ y x : ℝ, negativeBranch x y →
      1 / (4 * Real.sqrt (-x) * Real.sqrt (x * y ^ 2 - y ^ 3)) +
          Real.sqrt (-x) /
            (4 * Real.sqrt (y ^ 2) * threeHalves (x - y)) =
        1 / (4 * Real.sqrt (-x) * threeHalves (x - y)) := by
  intro y x h
  rcases h with ⟨hyx, hx⟩
  have hy : y < 0 := lt_trans hyx hx
  have hy0 : y ≠ 0 := ne_of_lt hy
  have hnx : 0 < -x := by linarith
  have hd : 0 < x - y := sub_pos.2 hyx
  have hsx : Real.sqrt (-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnx)
  have hsd : Real.sqrt (x - y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  rw [show x * y ^ 2 - y ^ 3 = y ^ 2 * (x - y) by ring]
  rw [sqrt_sq_mul y (x - y) (le_of_lt hd), Real.sqrt_sq_eq_abs,
    abs_of_neg hy, threeHalves_eq_mul_sqrt hd]
  field_simp [hy0, hsx, hsd] <;>
    nlinarith [Real.sq_sqrt (le_of_lt hnx),
      Real.sq_sqrt (le_of_lt hd)]

theorem gap25 :
    ∀ y x : ℝ, negativeBranch x y →
      mixedYX u x y =
        1 / (4 * Real.sqrt (-x) * threeHalves (x - y)) := by
  intro y x h
  exact (gap23 y x h).trans (gap24 y x h)

theorem gap26 :
    ∀ y x : ℝ, negativeBranch x y →
      mixedXY u x y = mixedYX u x y := by
  intro y x h
  rw [gap22 y x h, gap25 y x h]

theorem gap27 :
    ∀ x y : ℝ, admissible x y →
      mixedXY u x y = mixedYX u x y := by
  intro x y h
  rcases h with hpos | hneg
  · exact gap14 x y hpos
  · exact gap26 y x hneg

theorem gap28 :
    ∀ x y : ℝ, admissible x y →
      mixedXY u x y = mixedYX u x y := by
  exact gap27

end

end ProofGap.Exercise3228_2
