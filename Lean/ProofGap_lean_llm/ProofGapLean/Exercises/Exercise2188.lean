import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2188
noncomputable section

open Filter
open scoped BigOperators Interval

def h (x : ℝ) (n : ℕ) : ℝ := x / (n : ℝ)
def leftSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, h x n * Real.cos ((i : ℝ) * h x n)
def telescopingExpression (x : ℝ) (n : ℕ) : ℝ :=
  h x n / (2 * Real.sin (h x n / 2)) *
    (Real.sin (h x n / 2) +
      Real.sin (((2 * (n : ℝ) - 1) / 2) * h x n))
def normalizedExpression (x : ℝ) (n : ℕ) : ℝ :=
  (h x n / 2) / Real.sin (h x n / 2) *
    (Real.sin (x / (2 * (n : ℝ))) +
      Real.sin (((2 * (n : ℝ) - 1) * x) / (2 * (n : ℝ))))

private theorem cosine_sum_identity (a : ℝ) (n : ℕ) :
    2 * Real.sin (a / 2) *
        (∑ i ∈ Finset.range n, Real.cos ((i : ℝ) * a)) =
      Real.sin (a / 2) +
        Real.sin (((2 * (n : ℝ) - 1) / 2) * a) := by
  induction n with
  | zero =>
      simp [Real.sin_neg, div_eq_mul_inv, mul_comm]
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hold :
          (((2 * (n : ℝ) - 1) / 2) * a) =
            (n : ℝ) * a - a / 2 := by
        ring
      have hnew :
          (((2 * ((Nat.succ n : ℕ) : ℝ) - 1) / 2) * a) =
            (n : ℝ) * a + a / 2 := by
        rw [Nat.cast_succ]
        ring
      rw [hold, hnew, Real.sin_sub, Real.sin_add]
      ring

private theorem leftSum_eq_telescoping_of_sin_ne
    (x : ℝ) (n : ℕ) (hs : Real.sin (h x n / 2) ≠ 0) :
    leftSum x n = telescopingExpression x n := by
  unfold leftSum telescopingExpression
  rw [← Finset.mul_sum]
  rw [← cosine_sum_identity (h x n) n]
  field_simp [hs]
  <;> ring

private theorem telescopingExpression_eq_normalizedExpression
    (x : ℝ) (n : ℕ) :
    telescopingExpression x n = normalizedExpression x n := by
  unfold telescopingExpression normalizedExpression h
  ring_nf

private theorem intervalIntegral.integral_cos (a b : ℝ) :
    (∫ t in a..b, Real.cos t) = Real.sin b - Real.sin a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => Real.hasDerivAt_sin t)
    (Real.continuous_cos.intervalIntegrable a b)

theorem gap1 (x : ℝ) :
    Tendsto (leftSum x) atTop (nhds (Real.sin x)) ↔
      Tendsto (telescopingExpression x) atTop (nhds (Real.sin x)) := by
  by_cases hx : x = 0
  · subst x
    exact tendsto_congr' (Filter.Eventually.of_forall (fun n => by
      simp [leftSum, telescopingExpression, h]))
  · have hu :
        Tendsto (fun n : ℕ => h x n / 2) atTop (nhds 0) := by
      have ht :
          Tendsto (fun n : ℕ => (x / 2) / (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht
    have hsinc :
        Tendsto (fun n : ℕ => Real.sinc (h x n / 2)) atTop (nhds 1) := by
      simpa using ((Real.continuous_sinc.tendsto 0).comp hu)
    have hsinc_ne :
        ∀ᶠ n : ℕ in atTop, Real.sinc (h x n / 2) ≠ 0 :=
      hsinc.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
    apply tendsto_congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ), hsinc_ne] with n hn hsn
    have hn0_nat : n ≠ 0 := Nat.ne_of_gt hn
    have hn0 : (n : ℝ) ≠ 0 := by simpa using hn0_nat
    have hu_ne : h x n / 2 ≠ 0 := by
      exact div_ne_zero (div_ne_zero hx hn0) (by norm_num)
    have hsin : Real.sin (h x n / 2) ≠ 0 := by
      intro hzero
      apply hsn
      simp [Real.sinc, hu_ne, hzero]
    exact leftSum_eq_telescoping_of_sin_ne x n hsin

theorem gap2 (x : ℝ) :
    Tendsto (leftSum x) atTop (nhds (Real.sin x)) ↔
      Tendsto (normalizedExpression x) atTop (nhds (Real.sin x)) := by
  have heq : telescopingExpression x = normalizedExpression x :=
    funext (fun n => telescopingExpression_eq_normalizedExpression x n)
  simpa only [heq] using (gap1 x)

theorem gap3 (x : ℝ) :
    Tendsto (normalizedExpression x) atTop (nhds (Real.sin x)) := by
  by_cases hx : x = 0
  · subst x
    have heq : normalizedExpression 0 = fun _ : ℕ => (0 : ℝ) := by
      funext n
      simp [normalizedExpression, h]
    rw [heq]
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)))
  · have hu :
        Tendsto (fun n : ℕ => h x n / 2) atTop (nhds 0) := by
      have ht :
          Tendsto (fun n : ℕ => (x / 2) / (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [h, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht
    have hsinc :
        Tendsto (fun n : ℕ => Real.sinc (h x n / 2)) atTop (nhds 1) := by
      simpa using ((Real.continuous_sinc.tendsto 0).comp hu)
    have hinv :
        Tendsto (fun n : ℕ => (Real.sinc (h x n / 2))⁻¹) atTop (nhds 1) := by
      simpa using hsinc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hfactor :
        Tendsto
          (fun n : ℕ => (h x n / 2) / Real.sin (h x n / 2))
          atTop (nhds 1) := by
      apply hinv.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn0_nat : n ≠ 0 := Nat.ne_of_gt hn
      have hn0 : (n : ℝ) ≠ 0 := by simpa using hn0_nat
      have hu_ne : h x n / 2 ≠ 0 := by
        exact div_ne_zero (div_ne_zero hx hn0) (by norm_num)
      simp [Real.sinc, hu_ne]
    have hsinu :
        Tendsto (fun n : ℕ => Real.sin (h x n / 2)) atTop (nhds 0) := by
      simpa using ((Real.continuous_sin.tendsto 0).comp hu)
    have hxu :
        Tendsto (fun n : ℕ => x - h x n / 2) atTop (nhds x) := by
      simpa using (tendsto_const_nhds.sub hu)
    have hsin_xu :
        Tendsto (fun n : ℕ => Real.sin (x - h x n / 2))
          atTop (nhds (Real.sin x)) :=
      (Real.continuous_sin.tendsto x).comp hxu
    have hother :
        Tendsto
          (fun n : ℕ =>
            Real.sin (((2 * (n : ℝ) - 1) * x) / (2 * (n : ℝ))))
          atTop (nhds (Real.sin x)) := by
      apply hsin_xu.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn0_nat : n ≠ 0 := Nat.ne_of_gt hn
      have hn0 : (n : ℝ) ≠ 0 := by simpa using hn0_nat
      congr 1
      simp only [h]
      field_simp [hn0]
      <;> ring
    have hsum_eq :
        (fun n : ℕ =>
            Real.sin (h x n / 2) +
              Real.sin (((2 * (n : ℝ) - 1) * x) / (2 * (n : ℝ)))) =ᶠ[atTop]
          (fun n : ℕ =>
            Real.sin (x / (2 * (n : ℝ))) +
              Real.sin (((2 * (n : ℝ) - 1) * x) / (2 * (n : ℝ)))) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn0_nat : n ≠ 0 := Nat.ne_of_gt hn
      have hn0 : (n : ℝ) ≠ 0 := by simpa using hn0_nat
      have harg : h x n / 2 = x / (2 * (n : ℝ)) := by
        unfold h
        field_simp [hn0]
        <;> ring
      rw [harg]
    have hsum_base :
        Tendsto
          (fun n : ℕ =>
            Real.sin (h x n / 2) +
              Real.sin (((2 * (n : ℝ) - 1) * x) / (2 * (n : ℝ))))
          atTop (nhds (Real.sin x)) := by
      simpa only [zero_add] using hsinu.add hother
    have hsum :
        Tendsto
          (fun n : ℕ =>
            Real.sin (x / (2 * (n : ℝ))) +
              Real.sin (((2 * (n : ℝ) - 1) * x) / (2 * (n : ℝ))))
          atTop (nhds (Real.sin x)) :=
      (tendsto_congr' hsum_eq).1 hsum_base
    have hprod := hfactor.mul hsum
    simpa only [normalizedExpression, one_mul, zero_add] using hprod

theorem gap4 (x : ℝ) :
    Tendsto (leftSum x) atTop (nhds (Real.sin x)) := by
  exact (gap2 x).2 (gap3 x)

theorem gap5 (x : ℝ) :
    (∫ t in (0 : ℝ)..x, Real.cos t) = Real.sin x := by
  simpa using
    (intervalIntegral.integral_cos (a := (0 : ℝ)) (b := x))

end
end ProofGap.Exercise2188
