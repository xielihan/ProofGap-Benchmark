import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2218
noncomputable section

open Filter
open scoped BigOperators Interval

def wholeIntegrand (x : ℝ) : ℝ :=
  Real.sqrt (1 - Real.cos (2 * x))

def originalSeq (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    Real.sqrt n / ((n : ℝ) + ((k : ℝ) + 1))

def transformedSeq (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (1 / (1 + ((k : ℝ) + 1) / n)) * (1 / Real.sqrt n)

def riemannSeq (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (1 / (1 + ((k : ℝ) + 1) / n)) * (1 / (n : ℝ))

private theorem integral_partition_nat
    (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) :
    (∫ x in (0 : ℝ)..((n : ℝ) * Real.pi), f x) =
      ∑ k ∈ Finset.range n,
        ∫ x in ((k : ℝ) * Real.pi)..(((k : ℝ) + 1) * Real.pi), f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simpa [Nat.cast_succ] using
        (intervalIntegral.integral_add_adjacent_intervals
          (hf.intervalIntegrable (0 : ℝ) ((n : ℝ) * Real.pi))
          (hf.intervalIntegrable ((n : ℝ) * Real.pi)
            (((n : ℝ) + 1) * Real.pi))).symm

private theorem sqrt_sin_sq_periodic :
    Function.Periodic (fun x : ℝ => Real.sqrt (Real.sin x ^ 2)) Real.pi := by
  intro x
  simp [Real.sin_add_pi]

private theorem shifted_sqrt_sin_sq_integral (k : ℕ) :
    (∫ x in ((k : ℝ) * Real.pi)..(((k : ℝ) + 1) * Real.pi),
        Real.sqrt (Real.sin x ^ 2)) =
      ∫ x in (0 : ℝ)..Real.pi, Real.sqrt (Real.sin x ^ 2) := by
  have hshift :=
    sqrt_sin_sq_periodic.intervalIntegral_add_eq
      ((k : ℝ) * Real.pi) (0 : ℝ)
  simpa [add_mul, add_comm, add_left_comm, add_assoc] using hshift

private theorem integral_one_div_one_add :
    (∫ x in (0 : ℝ)..1, 1 / (1 + x)) = Real.log 2 := by
  have hcont :
      ContinuousOn (fun x : ℝ => 1 / (1 + x)) (Set.uIcc (0 : ℝ) 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact
      (continuousAt_const.div
        (continuousAt_const.add continuousAt_id)
        (by
          simp only [Pi.add_apply, id_eq]
          linarith [hx.1])).continuousWithinAt
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hxpos : 0 < 1 + x := by linarith [hx.1]
    simpa [one_div] using
      (Real.hasDerivAt_log (ne_of_gt hxpos)).comp x
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))
  calc
    (∫ x in (0 : ℝ)..1, 1 / (1 + x)) =
        Real.log (1 + 1) - Real.log (1 + 0) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        hderiv hcont.intervalIntegrable
    _ = Real.log 2 := by norm_num

private theorem integral_sin_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x) = 2 := by
  calc
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x) =
        -Real.cos Real.pi - (-Real.cos 0) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _hx => by simpa using (Real.hasDerivAt_cos x).neg)
        (Real.continuous_sin.intervalIntegrable (0 : ℝ) Real.pi)
    _ = 2 := by
      rw [Real.cos_pi]
      norm_num

private theorem sum_range_forward_difference
    (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (a (k + 1) - a k)) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem sum_range_backward_difference
    (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (a k - a (k + 1))) = a 0 - a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem log_increment_reciprocal_bounds
    (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧
      Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx1 : 0 < x + 1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx10 : x + 1 ≠ 0 := ne_of_gt hx1
  constructor
  · have h := Real.log_le_sub_one_of_pos (div_pos hx hx1)
    have hrat : x / (x + 1) - 1 = -(1 / (x + 1)) := by
      field_simp [hx10]
      <;> ring
    rw [Real.log_div hx0 hx10, hrat] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
    have hrat : (x + 1) / x - 1 = 1 / x := by
      field_simp [hx0]
      <;> ring
    rw [Real.log_div hx10 hx0, hrat] at h
    exact h

theorem gap1 :
    (∫ x in (0 : ℝ)..(100 * Real.pi), wholeIntegrand x) =
      ∑ k ∈ Finset.range 100,
        Real.sqrt 2 *
          (∫ x in ((k : ℝ) * Real.pi)..(((k : ℝ) + 1) * Real.pi),
            Real.sqrt (Real.sin x ^ 2)) := by
  let f : ℝ → ℝ := fun x => Real.sqrt (Real.sin x ^ 2)
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (Real.continuous_sin.pow 2)
  have hpoint : ∀ x : ℝ, wholeIntegrand x = Real.sqrt 2 * f x := by
    intro x
    have htrig : 1 - Real.cos (2 * x) = 2 * Real.sin x ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq x]
    dsimp [wholeIntegrand, f]
    rw [htrig, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (∫ x in (0 : ℝ)..(100 * Real.pi), wholeIntegrand x) =
        ∫ x in (0 : ℝ)..(100 * Real.pi), Real.sqrt 2 * f x := by
          apply intervalIntegral.integral_congr
          intro x _hx
          exact hpoint x
    _ = Real.sqrt 2 * (∫ x in (0 : ℝ)..(100 * Real.pi), f x) := by
          rw [intervalIntegral.integral_const_mul]
    _ = Real.sqrt 2 *
        (∑ k ∈ Finset.range 100,
          ∫ x in ((k : ℝ) * Real.pi)..(((k : ℝ) + 1) * Real.pi), f x) := by
          have hpart := integral_partition_nat f hf 100
          simpa using congrArg (fun z : ℝ => Real.sqrt 2 * z) hpart
    _ = ∑ k ∈ Finset.range 100,
        Real.sqrt 2 *
          (∫ x in ((k : ℝ) * Real.pi)..(((k : ℝ) + 1) * Real.pi),
            Real.sqrt (Real.sin x ^ 2)) := by
          rw [Finset.mul_sum]

theorem gap2 :
    (∫ x in (0 : ℝ)..(100 * Real.pi), wholeIntegrand x) =
      ∑ _k ∈ Finset.range 100,
        Real.sqrt 2 *
          (∫ x in (0 : ℝ)..Real.pi, Real.sqrt (Real.sin x ^ 2)) := by
  rw [gap1]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [shifted_sqrt_sin_sq_integral k]

theorem gap3 :
    (∑ _k ∈ Finset.range 100,
        Real.sqrt 2 *
          (∫ x in (0 : ℝ)..Real.pi, Real.sqrt (Real.sin x ^ 2))) =
      100 * Real.sqrt 2 *
        (∫ x in (0 : ℝ)..Real.pi, Real.sin x) := by
  have hi :
      (∫ x in (0 : ℝ)..Real.pi, Real.sqrt (Real.sin x ^ 2)) =
        ∫ x in (0 : ℝ)..Real.pi, Real.sin x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    dsimp
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2
  rw [hi]
  norm_num [Finset.sum_const]
  ring

theorem gap4 :
    100 * Real.sqrt 2 * (∫ x in (0 : ℝ)..Real.pi, Real.sin x) =
      200 * Real.sqrt 2 := by
  rw [integral_sin_zero_pi]
  ring

theorem gap5 :
    (∫ x in (0 : ℝ)..(100 * Real.pi), wholeIntegrand x) =
      200 * Real.sqrt 2 := by
  calc
    (∫ x in (0 : ℝ)..(100 * Real.pi), wholeIntegrand x) =
        ∑ _k ∈ Finset.range 100,
          Real.sqrt 2 *
            (∫ x in (0 : ℝ)..Real.pi, Real.sqrt (Real.sin x ^ 2)) := gap2
    _ = 100 * Real.sqrt 2 *
        (∫ x in (0 : ℝ)..Real.pi, Real.sin x) := gap3
    _ = 200 * Real.sqrt 2 := gap4

theorem gap6 (n : ℕ) :
    originalSeq n =
      ∑ k ∈ Finset.range n,
        Real.sqrt n / ((n : ℝ) + ((k : ℝ) + 1)) := by
  rfl

theorem gap7 (n : ℕ) (hn : 0 < n) :
    originalSeq n = transformedSeq n := by
  unfold originalSeq transformedSeq
  apply Finset.sum_congr rfl
  intro k _hk
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hs
  have hs_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hden : (n : ℝ) + ((k : ℝ) + 1) ≠ 0 := by positivity
  have hfrac : 1 + ((k : ℝ) + 1) / (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hs0, hden, hfrac]
  <;> nlinarith [hs_sq]

theorem gap8 :
    Tendsto riemannSeq atTop (nhds (Real.log 2)) := by
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_inv_atTop_zero :
          Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hlower :
      Tendsto (fun n : ℕ => Real.log 2 - 1 / (n : ℝ))
        atTop (nhds (Real.log 2)) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => Real.log 2) atTop (nhds (Real.log 2))).sub hinv)
  have hsandwich : ∀ᶠ n : ℕ in atTop,
      Real.log 2 - 1 / (n : ℝ) ≤ riemannSeq n ∧
        riemannSeq n ≤ Real.log 2 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hriem :
        riemannSeq n =
          ∑ k ∈ Finset.range n,
            1 / ((n : ℝ) + (k : ℝ) + 1) := by
      unfold riemannSeq
      apply Finset.sum_congr rfl
      intro k _hk
      have hfrac :
          1 + ((k : ℝ) + 1) / (n : ℝ) ≠ 0 := by positivity
      have hden :
          (n : ℝ) + (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn0, hfrac, hden]
      <;> ring
    have htel :
        (∑ k ∈ Finset.range n,
          (Real.log ((n : ℝ) + (k : ℝ) + 1) -
            Real.log ((n : ℝ) + (k : ℝ)))) = Real.log 2 := by
      calc
        (∑ k ∈ Finset.range n,
          (Real.log ((n : ℝ) + (k : ℝ) + 1) -
            Real.log ((n : ℝ) + (k : ℝ)))) =
            Real.log ((n : ℝ) + (n : ℝ)) - Real.log (n : ℝ) := by
              simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
                (sum_range_forward_difference
                  (fun j : ℕ => Real.log ((n : ℝ) + (j : ℝ))) n)
        _ = Real.log 2 := by
          have hadd : (n : ℝ) + (n : ℝ) = 2 * (n : ℝ) := by ring
          rw [hadd, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0]
          ring
    have hrecip :
        (∑ k ∈ Finset.range n,
          (1 / ((n : ℝ) + (k : ℝ)) -
            1 / ((n : ℝ) + (k : ℝ) + 1))) =
          1 / (n : ℝ) - 1 / ((n : ℝ) + (n : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
        (sum_range_backward_difference
          (fun j : ℕ => 1 / ((n : ℝ) + (j : ℝ))) n)
    have hrecip_le :
        (∑ k ∈ Finset.range n,
          (1 / ((n : ℝ) + (k : ℝ)) -
            1 / ((n : ℝ) + (k : ℝ) + 1))) ≤ 1 / (n : ℝ) := by
      rw [hrecip]
      have hnonneg : 0 ≤ 1 / ((n : ℝ) + (n : ℝ)) := by positivity
      linarith
    have hright :
        (∑ k ∈ Finset.range n,
          1 / ((n : ℝ) + (k : ℝ) + 1)) ≤
        ∑ k ∈ Finset.range n,
          (Real.log ((n : ℝ) + (k : ℝ) + 1) -
            Real.log ((n : ℝ) + (k : ℝ))) := by
      apply Finset.sum_le_sum
      intro k _hk
      have hx : 0 < (n : ℝ) + (k : ℝ) := by positivity
      exact (log_increment_reciprocal_bounds _ hx).1
    have hu :
        (∑ k ∈ Finset.range n,
          1 / ((n : ℝ) + (k : ℝ) + 1)) ≤ Real.log 2 := by
      calc
        (∑ k ∈ Finset.range n,
          1 / ((n : ℝ) + (k : ℝ) + 1)) ≤
            ∑ k ∈ Finset.range n,
              (Real.log ((n : ℝ) + (k : ℝ) + 1) -
                Real.log ((n : ℝ) + (k : ℝ))) := hright
        _ = Real.log 2 := htel
    have herr :
        (∑ k ∈ Finset.range n,
          ((Real.log ((n : ℝ) + (k : ℝ) + 1) -
              Real.log ((n : ℝ) + (k : ℝ))) -
            1 / ((n : ℝ) + (k : ℝ) + 1))) ≤
        ∑ k ∈ Finset.range n,
          (1 / ((n : ℝ) + (k : ℝ)) -
            1 / ((n : ℝ) + (k : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro k _hk
      have hx : 0 < (n : ℝ) + (k : ℝ) := by positivity
      exact sub_le_sub_right
        (log_increment_reciprocal_bounds _ hx).2 _
    have hdiff :
        Real.log 2 -
          (∑ k ∈ Finset.range n,
            1 / ((n : ℝ) + (k : ℝ) + 1)) ≤ 1 / (n : ℝ) := by
      calc
        Real.log 2 -
            (∑ k ∈ Finset.range n,
              1 / ((n : ℝ) + (k : ℝ) + 1)) =
            ∑ k ∈ Finset.range n,
              ((Real.log ((n : ℝ) + (k : ℝ) + 1) -
                  Real.log ((n : ℝ) + (k : ℝ))) -
                1 / ((n : ℝ) + (k : ℝ) + 1)) := by
                  rw [← htel, ← Finset.sum_sub_distrib]
        _ ≤ ∑ k ∈ Finset.range n,
              (1 / ((n : ℝ) + (k : ℝ)) -
                1 / ((n : ℝ) + (k : ℝ) + 1)) := herr
        _ ≤ 1 / (n : ℝ) := hrecip_le
    constructor
    · rw [hriem]
      linarith
    · rw [hriem]
      exact hu
  apply tendsto_order.2
  constructor
  · intro a ha
    have haevent :
        ∀ᶠ n : ℕ in atTop, a < Real.log 2 - 1 / (n : ℝ) :=
      (tendsto_order.1 hlower).1 a ha
    filter_upwards [haevent, hsandwich] with n han hs
    exact lt_of_lt_of_le han hs.1
  · intro b hb
    filter_upwards [hsandwich] with n hs
    exact lt_of_le_of_lt hs.2 hb

theorem gap9 :
    (∫ x in (0 : ℝ)..1, 1 / (1 + x)) = Real.log 2 := by
  exact integral_one_div_one_add

theorem gap10 :
    Tendsto riemannSeq atTop (nhds (Real.log 2)) := by
  exact gap8

theorem gap11 (n : ℕ) (hn : 0 < n) :
    transformedSeq n = Real.sqrt n * riemannSeq n := by
  unfold transformedSeq riemannSeq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hs
  have hs_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hfrac : 1 + ((k : ℝ) + 1) / (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hs0, hfrac]
  <;> nlinarith [hs_sq]

theorem gap12 :
    Tendsto (fun n : ℕ => Real.sqrt n * riemannSeq n) atTop atTop := by
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hbelow : c < Real.log 2 := by
    dsimp [c]
    linarith
  have hriemann : ∀ᶠ n in atTop, c < riemannSeq n :=
    (tendsto_order.1 gap10).1 c hbelow
  refine tendsto_atTop.2 ?_
  intro b
  have hroot : ∀ᶠ n : ℕ in atTop, b / c ≤ Real.sqrt (n : ℝ) := by
    exact hsqrt.eventually (eventually_ge_atTop (b / c))
  filter_upwards [hriemann, hroot] with n hn hnr
  have hsnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hb : b ≤ Real.sqrt (n : ℝ) * c :=
    (div_le_iff₀ hc).1 hnr
  calc
    b ≤ Real.sqrt (n : ℝ) * c := hb
    _ ≤ Real.sqrt (n : ℝ) * riemannSeq n :=
      mul_le_mul_of_nonneg_left (le_of_lt hn) hsnonneg

theorem gap13 :
    0 < Real.log 2 := by
  exact Real.log_pos (by norm_num)

theorem gap14 :
    Tendsto transformedSeq atTop atTop := by
  apply gap12.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (gap11 n hn).symm

theorem gap15 :
    Tendsto originalSeq atTop atTop := by
  apply gap14.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (gap7 n hn).symm

end
end ProofGap.Exercise2218
