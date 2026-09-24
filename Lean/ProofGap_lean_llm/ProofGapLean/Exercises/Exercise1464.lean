import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise1464

noncomputable section

open Filter

def f (x : ℝ) : ℝ := 3 * x ^ 4 - 4 * x ^ 3 - 6 * x ^ 2 + 12 * x - 20

def UniqueRootOn (u : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ x ∈ s, u x = 0 ∧ ∀ y ∈ s, u y = 0 → y = x

private theorem pg_continuous_f : Continuous f := by
  unfold f
  exact
    (((((continuous_const.mul (continuous_id.pow 4)).sub
      (continuous_const.mul (continuous_id.pow 3))).sub
      (continuous_const.mul (continuous_id.pow 2))).add
      (continuous_const.mul continuous_id)).sub continuous_const)

private theorem pg_strictAntiOn_left : StrictAntiOn f (Set.Iio (-1)) := by
  intro x hx y hy hxy
  have hy' : y < -1 := hy
  let u : ℝ := -1 - y
  let d : ℝ := y - x
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hd : 0 < d := by
    dsimp [d]
    linarith
  let B : ℝ :=
    3 * (4 * u ^ 3 + 6 * u ^ 2 * d + 4 * u * d ^ 2 + d ^ 3) +
    16 * (3 * u ^ 2 + 3 * u * d + d ^ 2) +
    24 * (2 * u + d)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hid : f x - f y = d * B := by
    dsimp [f, u, d, B]
    ring
  nlinarith [mul_pos hd hB]

private theorem pg_strictMonoOn_right : StrictMonoOn f (Set.Ioi 1) := by
  intro x hx y hy hxy
  have hx' : 1 < x := hx
  let u : ℝ := x - 1
  let d : ℝ := y - x
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hd : 0 < d := by
    dsimp [d]
    linarith
  let B : ℝ :=
    3 * (4 * u ^ 3 + 6 * u ^ 2 * d + 4 * u * d ^ 2 + d ^ 3) +
    8 * (3 * u ^ 2 + 3 * u * d + d ^ 2)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hid : f y - f x = d * B := by
    dsimp [f, u, d, B]
    ring
  nlinarith [mul_pos hd hB]

theorem gap1 (x : ℝ) :
    deriv f x = 12 * x ^ 3 - 12 * x ^ 2 - 12 * x + 12 := by
  have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    convert (hasDerivAt_id x).pow 4 using 1 <;> simp only [id_eq] <;> ring
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_id x).pow 3 using 1 <;> simp only [id_eq] <;> ring
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp only [id_eq] <;> ring
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hf : HasDerivAt
      (fun y : ℝ => 3 * y ^ 4 - 4 * y ^ 3 - 6 * y ^ 2 + 12 * y - 20)
      (12 * x ^ 3 - 12 * x ^ 2 - 12 * x + 12) x := by
    convert ((((h4.const_mul 3).sub (h3.const_mul 4)).sub
      (h2.const_mul 6)).add (h1.const_mul 12)).sub_const 20 using 1 <;> ring
  simpa only [f] using hf.deriv

theorem gap2 (x : ℝ) (hzero : deriv f x = 0) :
    x = -1 ∨ x = 1 := by
  rw [gap1] at hzero
  have hfactor :
      12 * x ^ 3 - 12 * x ^ 2 - 12 * x + 12 =
        (12 * (x + 1)) * (x - 1) ^ 2 := by
    ring
  rw [hfactor] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h12 | hx
    · norm_num at h12
    · left
      linarith
  · have hx : x - 1 = 0 := eq_zero_of_pow_eq_zero h
    right
    linarith

theorem gap3 :
    Tendsto f atBot atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_le_atBot (min (-3) (-b))] with x hx
  have hxneg : x ≤ -3 := le_trans hx (min_le_left _ _)
  have hbx : b ≤ -x := by
    have : x ≤ -b := le_trans hx (min_le_right _ _)
    linarith
  let z : ℝ := -3 - x
  have hz : 0 ≤ z := by
    dsimp [z]
    linarith
  have hform :
      f x = 241 + 384 * z + 192 * z ^ 2 + 40 * z ^ 3 + 3 * z ^ 4 := by
    dsimp [f, z]
    ring
  have hxz : -x = z + 3 := by
    dsimp [z]
    ring
  have hbase : -x ≤ f x := by
    rw [hxz, hform]
    nlinarith [pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4]
  exact hbx.trans hbase

theorem gap4 :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (max 3 b)] with x hx
  have hxpos : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hbx : b ≤ x := le_trans (le_max_right _ _) hx
  let z : ℝ := x - 3
  have hz : 0 ≤ z := by
    dsimp [z]
    linarith
  have hform :
      f x = 97 + 192 * z + 120 * z ^ 2 + 32 * z ^ 3 + 3 * z ^ 4 := by
    dsimp [f, z]
    ring
  have hxz : x = z + 3 := by
    dsimp [z]
    ring
  have hbase : x ≤ f x := by
    calc
      x = z + 3 := hxz
      _ ≤ 97 + 192 * z + 120 * z ^ 2 + 32 * z ^ 3 + 3 * z ^ 4 := by
        nlinarith [pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4]
      _ = f x := hform.symm
  exact hbx.trans hbase

theorem gap5 :
    f (-1) = -31 := by
  norm_num [f]

theorem gap6 :
    (-31 : ℝ) < 0 := by
  norm_num

theorem gap7 :
    f 1 = -15 := by
  norm_num [f]

theorem gap8 :
    (-15 : ℝ) < 0 := by
  norm_num

theorem gap9 (x : ℝ) (hx : x < -1) :
    deriv f x < 0 := by
  calc
    deriv f x = (12 * (x + 1)) * (x - 1) ^ 2 := by
      rw [gap1]
      ring
    _ < 0 := by
      have hleft : 12 * (x + 1) < 0 := by
        nlinarith
      have hsq : 0 < (x - 1) ^ 2 := by
        have : x - 1 ≠ 0 := by linarith
        positivity
      exact mul_neg_of_neg_of_pos hleft hsq

theorem gap10 (x : ℝ) (hx : -1 < x) (hne : x ≠ 1) :
    deriv f x > 0 := by
  calc
    deriv f x = (12 * (x + 1)) * (x - 1) ^ 2 := by
      rw [gap1]
      ring
    _ > 0 := by
      have hleft : 0 < 12 * (x + 1) := by
        nlinarith
      have hxone : x - 1 ≠ 0 := sub_ne_zero.mpr hne
      have hsq : 0 < (x - 1) ^ 2 := by
        positivity
      exact mul_pos hleft hsq

theorem gap11 :
    UniqueRootOn f (Set.Iio (-1)) := by
  have hz :
      (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => -f t) (-3))
        ((fun t : ℝ => -f t) (-1)) := by
    constructor <;> norm_num [f]
  have himg :
      (0 : ℝ) ∈ (fun t : ℝ => -f t) '' Set.Icc (-3) (-1) :=
    (intermediate_value_Icc
      (f := fun t : ℝ => -f t)
      (by norm_num : (-3 : ℝ) ≤ -1)
      pg_continuous_f.neg.continuousOn) hz
  rcases himg with ⟨x, hx, hxzero⟩
  have hfx : f x = 0 := by
    change -f x = 0 at hxzero
    linarith
  have hxne : x ≠ -1 := by
    intro h
    rw [h] at hfx
    norm_num [f] at hfx
  have hxmem : x < -1 := lt_of_le_of_ne hx.2 hxne
  refine ⟨x, hxmem, hfx, ?_⟩
  intro y hymem hyzero
  exact pg_strictAntiOn_left.injOn hymem hxmem (hyzero.trans hfx.symm)

theorem gap12 :
    UniqueRootOn f (Set.Ioi 1) := by
  have hz : (0 : ℝ) ∈ Set.Icc (f 1) (f 3) := by
    constructor <;> norm_num [f]
  have himg : (0 : ℝ) ∈ f '' Set.Icc 1 3 :=
    (intermediate_value_Icc
      (f := f)
      (by norm_num : (1 : ℝ) ≤ 3)
      pg_continuous_f.continuousOn) hz
  rcases himg with ⟨x, hx, hfx⟩
  have hxne : x ≠ 1 := by
    intro h
    rw [h] at hfx
    norm_num [f] at hfx
  have hxmem : 1 < x := lt_of_le_of_ne hx.1 (Ne.symm hxne)
  refine ⟨x, hxmem, hfx, ?_⟩
  intro y hymem hyzero
  exact pg_strictMonoOn_right.injOn hymem hxmem (hyzero.trans hfx.symm)

theorem gap13 (x : ℝ) :
    x ∈ {y : ℝ | (y < -1 ∨ 1 < y) ∧ f y = 0} ↔
      3 * x ^ 4 - 4 * x ^ 3 - 6 * x ^ 2 + 12 * x - 20 = 0 := by
  constructor
  · rintro ⟨_, hfx⟩
    simpa [f] using hfx
  · intro hxpoly
    have hfx : f x = 0 := by
      simpa [f] using hxpoly
    refine ⟨?_, hfx⟩
    by_contra hout
    have hxl : -1 ≤ x := le_of_not_gt (fun h => hout (Or.inl h))
    have hxr : x ≤ 1 := le_of_not_gt (fun h => hout (Or.inr h))
    let z : ℝ := 1 - x
    have hz : 0 ≤ z := by
      dsimp [z]
      linarith
    have hzle : z ≤ 2 := by
      dsimp [z]
      linarith
    have hcoef : 3 * z - 8 ≤ 0 := by linarith
    have hprod : z ^ 3 * (3 * z - 8) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hz 3) hcoef
    have hform : f x = -15 + z ^ 3 * (3 * z - 8) := by
      dsimp [f, z]
      ring
    have hneg : f x < 0 := by
      rw [hform]
      linarith
    exact (ne_of_lt hneg) hfx

end

end ProofGap.Exercise1464
