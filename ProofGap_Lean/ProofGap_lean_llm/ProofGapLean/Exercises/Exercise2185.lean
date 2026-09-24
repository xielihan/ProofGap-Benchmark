import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise2185
noncomputable section

open Filter
open scoped BigOperators Interval

def h (n : ℕ) : ℝ := 3 / (n : ℝ)
def leftSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 + (i : ℝ) * h n) ^ 2 * h n

theorem gap1 (n : ℕ) (hn : 0 < n) :
    leftSum n =
      ∑ i ∈ Finset.range n, (-1 + (i : ℝ) * h n) ^ 2 * h n := by
  rfl

theorem gap2 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, (-1 + (i : ℝ) * h n) ^ 2 * h n) =
      (n : ℝ) * h n
      - 2 * (h n) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ))
      + (h n) ^ 3 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) := by
  calc
    (∑ i ∈ Finset.range n, (-1 + (i : ℝ) * h n) ^ 2 * h n) =
        ∑ i ∈ Finset.range n,
          (h n - (2 * (h n) ^ 2) * (i : ℝ) +
            (h n) ^ 3 * (i : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ Finset.range n, h n) -
          (2 * (h n) ^ 2) * (∑ i ∈ Finset.range n, (i : ℝ)) +
          (h n) ^ 3 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (n : ℝ) * h n
          - 2 * (h n) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ))
          + (h n) ^ 3 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) := by
      simp

theorem gap3 (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * h n
      - 2 * (h n) ^ 2 * (∑ i ∈ Finset.range n, (i : ℝ))
      + (h n) ^ 3 * (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) =
      3 + (9 - 9 * (n : ℝ)) / (2 * (n : ℝ) ^ 2) := by
  have hsum1 : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, (i : ℝ)) =
        (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        simp only [Finset.sum_range_succ, ih, Nat.cast_succ]
        ring
  have hsum2 : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, (i : ℝ) ^ 2) =
        (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) / 6 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        simp only [Finset.sum_range_succ, ih, Nat.cast_succ]
        ring
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [hsum1 n, hsum2 n]
  unfold h
  field_simp [hn0] <;> ring

theorem gap4 (n : ℕ) (hn : 0 < n) :
    leftSum n = 3 + (9 - 9 * (n : ℝ)) / (2 * (n : ℝ) ^ 2) := by
  exact (gap1 n hn).trans ((gap2 n hn).trans (gap3 n hn))

theorem gap5 :
    Tendsto leftSum atTop (nhds (3 : ℝ)) := by
  have hn_top :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hn_top
  have hconst :
      Tendsto (fun _ : ℕ => (9 / 2 : ℝ)) atTop (nhds (9 / 2)) :=
    tendsto_const_nhds
  have hmodel :
      Tendsto
        (fun n : ℕ =>
          (9 / 2 : ℝ) *
            ((n : ℝ)⁻¹ * (n : ℝ)⁻¹ - (n : ℝ)⁻¹))
        atTop (nhds 0) := by
    simpa using hconst.mul ((hinv.mul hinv).sub hinv)
  have hcorr :
      Tendsto
        (fun n : ℕ =>
          (9 - 9 * (n : ℝ)) / (2 * (n : ℝ) ^ 2))
        atTop (nhds 0) := by
    refine (tendsto_congr' ?_).2 hmodel
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0] <;> ring
  have hconst3 :
      Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) :=
    tendsto_const_nhds
  have hformula :
      Tendsto
        (fun n : ℕ =>
          3 + (9 - 9 * (n : ℝ)) / (2 * (n : ℝ) ^ 2))
        atTop (nhds 3) := by
    simpa using hconst3.add hcorr
  have heq :
      leftSum =ᶠ[atTop]
        (fun n : ℕ =>
          3 + (9 - 9 * (n : ℝ)) / (2 * (n : ℝ) ^ 2)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact gap4 n hn
  exact (tendsto_congr' heq).2 hformula

theorem gap6 :
    ContinuousOn (fun x : ℝ => x ^ 2) (Set.Icc (-1) 2) := by
  exact (continuous_id.pow 2).continuousOn

theorem gap7 :
    (∫ x in (-1 : ℝ)..2, x ^ 2) = 3 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
    intro x
    convert ((hasDerivAt_id x).pow 3).div_const 3 using 1 <;> ring
    rfl
  calc
    (∫ x in (-1 : ℝ)..2, x ^ 2) =
        (2 : ℝ) ^ 3 / 3 - (-1 : ℝ) ^ 3 / 3 := by
      refine intervalIntegral.integral_deriv_eq_sub'
        (fun y : ℝ => y ^ 3 / 3) ?_ ?_ ?_
      · funext x
        exact (hderiv x).deriv
      · intro x hx
        exact (hderiv x).differentiableAt
      · exact (continuous_id.pow 2).continuousOn
    _ = 3 := by norm_num

end
end ProofGap.Exercise2185
