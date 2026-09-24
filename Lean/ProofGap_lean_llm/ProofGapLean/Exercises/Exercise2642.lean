import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise2642

noncomputable section

open Filter

def argument (a : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (-a)

def term (a : ℝ) (n : ℕ) : ℝ :=
  Real.log (argument a n) - Real.log (Real.sin (argument a n))

def comparison (a : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (2 * a)

def converges (a : ℝ) : Prop :=
  Summable (fun n : ℕ => term a (n + 1))

private theorem tendsto_sub_sin_div_cube :
    Tendsto (fun x : ℝ => (x - Real.sin x) / x ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 6)) := by
  have hpoly (x : ℝ) :
      taylorWithinEval Real.sin 3 Set.univ 0 x = x - x ^ 3 / 6 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, iteratedDerivWithin_univ,
      Real.iteratedDeriv_odd_sin, Real.iteratedDeriv_even_sin]
    ring
  have ht := Real.taylor_tendsto (f := Real.sin) (x₀ := 0) (n := 3)
    convex_univ (Set.mem_univ 0) Real.contDiff_sin.contDiffOn
  have ht' :
      Tendsto (fun x : ℝ =>
        (Real.sin x - (x - x ^ 3 / 6)) / x ^ 3)
        (nhds 0) (nhds 0) := by
    convert ht using 1 <;> simp [hpoly] <;> ring
  have h := (tendsto_const_nhds (x := (1 / 6 : ℝ))).sub ht'
  have hright :
      Tendsto (fun x : ℝ =>
        1 / 6 - (Real.sin x - (x - x ^ 3 / 6)) / x ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 6)) := by
    simpa only [sub_zero] using h.mono_left inf_le_left
  refine hright.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx.ne'
  field_simp
  ring

private theorem tendsto_div_sin :
    Tendsto (fun x : ℝ => x / Real.sin x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsin_div :
      Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
  simpa only [inv_div, inv_one] using hsin_div.inv₀ one_ne_zero

private theorem tendsto_log_one_add_div :
    Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero_right

private theorem tendsto_div_sin_sub_one_div_sq :
    Tendsto (fun x : ℝ => (x / Real.sin x - 1) / x ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 6)) := by
  have h := tendsto_sub_sin_div_cube.mul tendsto_div_sin
  simp only [mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds Real.pi_pos)]
      with x hx hxp
  have hx0 : x ≠ 0 := hx.ne'
  have hsin : Real.sin x ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hx hxp).ne'
  field_simp

theorem gap1 (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ a := by
  exact ha

theorem gap2 (a : ℝ) (ha : a = 0) (n : ℕ) (hn : 1 ≤ n) :
    term a n = -Real.log (Real.sin 1) := by
  subst a
  simp [term, argument]

theorem gap3 :
    0 < -Real.log (Real.sin 1) := by
  have hsinpos : 0 < Real.sin 1 :=
    Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  have hsinlt : Real.sin 1 < 1 := Real.sin_lt (by norm_num)
  linarith [Real.log_neg hsinpos hsinlt]

theorem gap4 (a : ℝ) (ha : a = 0) :
    ¬ converges a := by
  intro hs
  have hzero : Tendsto (fun n : ℕ => term a (n + 1)) atTop (nhds 0) := by
    simpa only [Nat.cofinite_eq_atTop] using hs.tendsto_cofinite_zero
  have hconst : Tendsto (fun n : ℕ => term a (n + 1)) atTop
      (nhds (-Real.log (Real.sin 1))) := by
    have heq : (fun n : ℕ => term a (n + 1)) =
        (fun _ : ℕ => -Real.log (Real.sin 1)) := by
      funext n
      exact gap2 a ha (n + 1) (by omega)
    rw [heq]
    exact tendsto_const_nhds
  have heq : -Real.log (Real.sin 1) = 0 := tendsto_nhds_unique hconst hzero
  linarith [gap3]

theorem gap5 (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    term a n =
      Real.log (argument a n / Real.sin (argument a n)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have harg : 0 < argument a n := by
    exact Real.rpow_pos_of_pos hnpos _
  have harg_le : argument a n ≤ 1 := by
    unfold argument
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  have hsin : 0 < Real.sin (argument a n) :=
    Real.sin_pos_of_pos_of_lt_pi harg
      (harg_le.trans_lt (by linarith [Real.pi_gt_three]))
  unfold term
  rw [Real.log_div harg.ne' hsin.ne']

theorem gap6 (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun x : ℝ =>
        ((Real.rpow x a / Real.sin (Real.rpow x a)) - 1) /
          Real.rpow x (2 * a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 6)) := by
  have hzero : Tendsto (fun x : ℝ => x ^ a) (nhds 0) (nhds 0) := by
    simpa [Real.zero_rpow ha.ne'] using
      (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  have hrpow :
      Tendsto (fun x : ℝ => x ^ a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero.mono_left inf_le_left, by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.rpow_pos_of_pos hx a⟩
  have h := tendsto_div_sin_sub_one_div_sq.comp hrpow
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hpow : Real.rpow x (2 * a) = (Real.rpow x a) ^ 2 := by
    rw [mul_comm]
    exact Real.rpow_mul_natCast hx.le a 2
  simp only [Function.comp_apply, hpow]
  change
    (Real.rpow x a / Real.sin (Real.rpow x a) - 1) / (Real.rpow x a) ^ 2 =
      (Real.rpow x a / Real.sin (Real.rpow x a) - 1) / (Real.rpow x a) ^ 2
  rfl

private theorem tendsto_log_sin_ratio (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun x : ℝ =>
        Real.log (Real.rpow x a / Real.sin (Real.rpow x a)) /
          Real.rpow x (2 * a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 6)) := by
  have hzero : Tendsto (fun x : ℝ => x ^ a) (nhds 0) (nhds 0) := by
    simpa [Real.zero_rpow ha.ne'] using
      (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  have hrpow :
      Tendsto (fun x : ℝ => x ^ a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero.mono_left inf_le_left, by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.rpow_pos_of_pos hx a⟩
  let q : ℝ → ℝ := fun x => x ^ a / Real.sin (x ^ a)
  have hq : Tendsto q (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [q] using tendsto_div_sin.comp hrpow
  have hy0 : Tendsto (fun x => q x - 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hq.sub_const 1
  have hypos : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), 0 < q x - 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (hzero.mono_left inf_le_left).eventually (Iio_mem_nhds Real.pi_pos)]
        with x hx hxp
    have ht : 0 < x ^ a := Real.rpow_pos_of_pos hx a
    have hs : 0 < Real.sin (x ^ a) :=
      Real.sin_pos_of_pos_of_lt_pi ht hxp
    have hlt : Real.sin (x ^ a) < x ^ a := Real.sin_lt ht
    dsimp [q]
    exact sub_pos.mpr ((one_lt_div₀ hs).mpr hlt)
  have hy : Tendsto (fun x => q x - 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy0, hypos⟩
  have hlog := tendsto_log_one_add_div.comp hy
  have h := hlog.mul (gap6 a ha)
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [hypos, self_mem_nhdsWithin] with x hyx hx
  have hyne : q x - 1 ≠ 0 := hyx.ne'
  have hxpow : Real.rpow x (2 * a) ≠ 0 :=
    (Real.rpow_pos_of_pos hx (2 * a)).ne'
  dsimp [q] at hyne ⊢
  rw [show 1 + (x ^ a / Real.sin (x ^ a) - 1) =
      x ^ a / Real.sin (x ^ a) by ring]
  field_simp

theorem gap7 (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ => term a (n + 1) / comparison a (n + 1))
      atTop (nhds (1 / 6)) := by
  have htop :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hu0 :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    htop.inv_tendsto_atTop
  have hu :
      Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹)
        atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu0, by
      filter_upwards with n
      have hb : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos n
      exact inv_pos.mpr hb⟩
  have h := (tendsto_log_sin_ratio a ha).comp hu
  refine h.congr' ?_
  filter_upwards with n
  have hb : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  have harg :
      Real.rpow ((((n + 1 : ℕ) : ℝ))⁻¹) a = argument a (n + 1) := by
    calc
      Real.rpow ((((n + 1 : ℕ) : ℝ))⁻¹) a =
          (Real.rpow (((n + 1 : ℕ) : ℝ)) a)⁻¹ :=
        Real.inv_rpow hb.le a
      _ = Real.rpow (((n + 1 : ℕ) : ℝ)) (-a) :=
        (Real.rpow_neg hb.le a).symm
      _ = argument a (n + 1) := rfl
  have hden :
      Real.rpow ((((n + 1 : ℕ) : ℝ))⁻¹) (2 * a) =
        comparison a (n + 1) := by
    calc
      Real.rpow ((((n + 1 : ℕ) : ℝ))⁻¹) (2 * a) =
          (Real.rpow (((n + 1 : ℕ) : ℝ)) (2 * a))⁻¹ :=
        Real.inv_rpow hb.le (2 * a)
      _ = 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) (2 * a) := by simp [one_div]
      _ = comparison a (n + 1) := rfl
  simp only [Function.comp_apply]
  rw [harg, hden, gap5 a ha (n + 1) (by omega)]

private theorem comparison_pos (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 < comparison a n := by
  unfold comparison
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact one_div_pos.mpr (Real.rpow_pos_of_pos hnpos _)

private theorem term_nonneg_of_pos (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ term a n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have harg : 0 < argument a n := Real.rpow_pos_of_pos hnpos _
  have harg_le : argument a n ≤ 1 := by
    unfold argument
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
  have hsin : 0 < Real.sin (argument a n) :=
    Real.sin_pos_of_pos_of_lt_pi harg
      (harg_le.trans_lt (by linarith [Real.pi_gt_three]))
  have hratio : 1 ≤ argument a n / Real.sin (argument a n) := by
    apply (le_div_iff₀ hsin).mpr
    simpa using (Real.sin_lt harg).le
  rw [gap5 a ha n hn]
  exact (Real.log_nonneg_iff (div_pos harg hsin)).mpr hratio

theorem gap8 (a : ℝ) (ha : 0 < a) (hexp : 1 < 2 * a) :
    converges a := by
  have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 * a))) :=
    Real.summable_one_div_nat_rpow.mpr hexp
  have hcomp : Summable (fun n : ℕ => comparison a (n + 1)) := by
    have hshift :
        Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ (2 * a))) :=
      (summable_nat_add_iff 1).mpr hfull
    simpa [comparison] using hshift
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        term a (n + 1) / comparison a (n + 1) < 1 :=
    (tendsto_order.mp (gap7 a ha)).2 1 (by norm_num)
  unfold converges
  refine hcomp.of_norm_bounded_eventually_nat ?_
  filter_upwards [hupper] with n hn
  have hp := comparison_pos a (n + 1) (by omega)
  have hle : term a (n + 1) ≤ comparison a (n + 1) := by
    have := (div_lt_iff₀ hp).mp hn
    linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (term_nonneg_of_pos a ha (n + 1) (by omega))]
  exact hle

theorem gap9 (a : ℝ) (ha : 0 < a) (hexp : 2 * a ≤ 1) :
    ¬ converges a := by
  intro hs
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        (1 / 12 : ℝ) < term a (n + 1) / comparison a (n + 1) :=
    (tendsto_order.mp (gap7 a ha)).1 (1 / 12) (by norm_num)
  have hscaled : Summable (fun n : ℕ => 12 * term a (n + 1)) :=
    hs.mul_left 12
  have hcomp : Summable (fun n : ℕ => comparison a (n + 1)) :=
    hscaled.of_norm_bounded_eventually_nat (by
      filter_upwards [hlower] with n hn
      have hp := comparison_pos a (n + 1) (by omega)
      have hle := (lt_div_iff₀ hp).mp hn
      rw [Real.norm_eq_abs, abs_of_nonneg hp.le]
      nlinarith)
  have hcomp' :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ (2 * a))) := by
    simpa [comparison] using hcomp
  have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 * a))) :=
    (summable_nat_add_iff 1).mp hcomp'
  have : 1 < 2 * a := Real.summable_one_div_nat_rpow.mp hfull
  linarith

private theorem not_converges_of_neg (a : ℝ) (ha : a < 0) :
    ¬ converges a := by
  intro hs
  have hcast : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlower : Tendsto
      (fun n : ℕ => (-a) * Real.log (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp hcast).const_mul_atTop (neg_pos.mpr ha)
  have hterm : Tendsto (fun n : ℕ => term a (n + 1)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlower
    filter_upwards with n
    have hb : 0 < (((n + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.succ_pos n
    have hlogsine : Real.log (Real.sin (argument a (n + 1))) ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one _)
    have hlogarg : Real.log (argument a (n + 1)) =
        (-a) * Real.log (((n + 1 : ℕ) : ℝ)) := by
      unfold argument
      exact Real.log_rpow hb (-a)
    unfold term
    rw [hlogarg]
    linarith
  have hzero : Tendsto (fun n : ℕ => term a (n + 1)) atTop (nhds 0) := by
    simpa only [Nat.cofinite_eq_atTop] using hs.tendsto_cofinite_zero
  exact not_tendsto_nhds_of_tendsto_atTop hterm 0 hzero

theorem gap10 (a : ℝ) :
    a ∈ {r : ℝ | 1 / 2 < r} ↔ converges a := by
  change 1 / 2 < a ↔ converges a
  constructor
  · intro ha
    exact gap8 a (by linarith) (by linarith)
  · intro hs
    by_contra hnot
    have hle : a ≤ 1 / 2 := le_of_not_gt hnot
    by_cases hneg : a < 0
    · exact not_converges_of_neg a hneg hs
    have hnonneg : 0 ≤ a := le_of_not_gt hneg
    rcases hnonneg.eq_or_lt with hzero | hpos
    · exact gap4 a hzero.symm hs
    · exact gap9 a hpos (by linarith) hs

end

end ProofGap.Exercise2642
