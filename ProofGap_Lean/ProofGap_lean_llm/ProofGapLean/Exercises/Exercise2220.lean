import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2220
noncomputable section

open Filter
open scoped BigOperators Interval

def tailSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, 1 / ((n : ℝ) + ((i : ℝ) + 1))

def riemannSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (1 / (1 + ((i : ℝ) + 1) / n)) * (1 / (n : ℝ))

private theorem integral_one_div_one_add :
    (∫ x in (0 : ℝ)..1, 1 / (1 + x)) = Real.log 2 := by
  have hcont :
      ContinuousOn (fun x : ℝ => 1 / (1 + x)) (Set.uIcc (0 : ℝ) 1) := by
    have hnum :
        ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.uIcc (0 : ℝ) 1) :=
      continuousOn_const
    have hden :
        ContinuousOn (fun x : ℝ => 1 + x) (Set.uIcc (0 : ℝ) 1) :=
      continuousOn_const.add continuousOn_id
    refine hnum.div hden ?_
    intro x hx hzero
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    linarith [hx.1]
  calc
    (∫ x in (0 : ℝ)..1, 1 / (1 + x)) =
        Real.log (1 + 1) - Real.log (1 + 0) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun x : ℝ => Real.log (1 + x))
        (f' := fun x : ℝ => 1 / (1 + x)) ?_ hcont.intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hne : 1 + x ≠ 0 := by
        linarith [hx.1]
      simpa [one_div] using
        (Real.hasDerivAt_log hne).comp x
          ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))
    _ = Real.log 2 := by norm_num

private theorem sum_step_sub (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f (i + 1) - f i)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem sum_sub_step (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f i - f (i + 1))) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem log_increment_bounds {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧
      Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx1 : 0 < x + 1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx10 : x + 1 ≠ 0 := ne_of_gt hx1
  constructor
  · have h := Real.log_le_sub_one_of_pos (div_pos hx hx1)
    rw [Real.log_div hx0 hx10] at h
    have hq : x / (x + 1) - 1 = -(1 / (x + 1)) := by
      field_simp [hx0, hx10]
      <;> ring
    rw [hq] at h
    linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
    rw [Real.log_div hx10 hx0] at h
    have hq : (x + 1) / x - 1 = 1 / x := by
      field_simp [hx0, hx10]
      <;> ring
    rw [hq] at h
    linarith

private theorem tailSum_bounds (n : ℕ) (hn : 0 < n) :
    Real.log 2 - 1 / (n : ℝ) ≤ tailSum n ∧
      tailSum n ≤ Real.log 2 := by
  let L : ℕ → ℝ := fun i => Real.log ((n : ℝ) + (i : ℝ))
  let R : ℕ → ℝ := fun i => 1 / ((n : ℝ) + (i : ℝ))
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hlower (i : ℕ) : R (i + 1) ≤ L (i + 1) - L i := by
    have hx : 0 < (n : ℝ) + (i : ℝ) :=
      add_pos_of_pos_of_nonneg hnR (Nat.cast_nonneg i)
    simpa [L, R, Nat.cast_succ, add_assoc] using
      (log_increment_bounds hx).1
  have hupper (i : ℕ) : L (i + 1) - L i ≤ R i := by
    have hx : 0 < (n : ℝ) + (i : ℝ) :=
      add_pos_of_pos_of_nonneg hnR (Nat.cast_nonneg i)
    simpa [L, R, Nat.cast_succ, add_assoc] using
      (log_increment_bounds hx).2
  have hlogsum :
      (∑ i ∈ Finset.range n, (L (i + 1) - L i)) = Real.log 2 := by
    rw [sum_step_sub]
    simp only [L, Nat.cast_zero, add_zero]
    have hnn0 : (n : ℝ) + (n : ℝ) ≠ 0 := by
      exact ne_of_gt (add_pos hnR hnR)
    rw [← Real.log_div hnn0 hn0]
    congr 1
    field_simp [hn0, hnn0]
    <;> ring
  have hsumR :
      (∑ i ∈ Finset.range n, R (i + 1)) = tailSum n := by
    unfold tailSum
    apply Finset.sum_congr rfl
    intro i hi
    simp [R, Nat.cast_succ]
  constructor
  · have hs :
        (∑ i ∈ Finset.range n, (L (i + 1) - L i)) ≤
          (∑ i ∈ Finset.range n, R (i + 1)) +
            ∑ i ∈ Finset.range n, (R i - R (i + 1)) := by
      calc
        (∑ i ∈ Finset.range n, (L (i + 1) - L i)) ≤
            ∑ i ∈ Finset.range n,
              (R (i + 1) + (R i - R (i + 1))) := by
          apply Finset.sum_le_sum
          intro i hi
          linarith [hupper i]
        _ = (∑ i ∈ Finset.range n, R (i + 1)) +
              ∑ i ∈ Finset.range n, (R i - R (i + 1)) := by
          rw [Finset.sum_add_distrib]
    have herrsum :
        (∑ i ∈ Finset.range n, (R i - R (i + 1))) = R 0 - R n :=
      sum_sub_step R n
    rw [hlogsum, hsumR, herrsum] at hs
    have hR0 : R 0 = 1 / (n : ℝ) := by simp [R]
    have hRn : 0 ≤ R n := by
      apply one_div_nonneg.mpr
      dsimp [R]
      exact le_of_lt
        (add_pos_of_pos_of_nonneg hnR (Nat.cast_nonneg n))
    rw [hR0] at hs
    linarith
  · rw [← hsumR, ← hlogsum]
    apply Finset.sum_le_sum
    intro i hi
    exact hlower i

private theorem tailSum_tendsto :
    Tendsto tailSum atTop (nhds (Real.log 2)) := by
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hlower :
      Tendsto (fun n : ℕ => Real.log 2 - 1 / (n : ℝ))
        atTop (nhds (Real.log 2)) := by
    simpa using (tendsto_const_nhds.sub hinv)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (tailSum_bounds n hn).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (tailSum_bounds n hn).2

theorem gap1 (n : ℕ) (hn : 0 < n) :
    tailSum n = riemannSum n := by
  unfold tailSum riemannSum
  apply Finset.sum_congr rfl
  intro i hi
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hiR : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hden : (n : ℝ) + ((i : ℝ) + 1) ≠ 0 := by
    apply ne_of_gt
    linarith
  field_simp [hn0, hden]

theorem gap2 :
    Tendsto riemannSum atTop (nhds (Real.log 2)) := by
  apply tailSum_tendsto.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact gap1 n hn

theorem gap3 :
    (∫ x in (0 : ℝ)..1, 1 / (1 + x)) = Real.log 2 := by
  exact integral_one_div_one_add

theorem gap4 :
    Tendsto tailSum atTop (nhds (Real.log 2)) := by
  exact tailSum_tendsto

end
end ProofGap.Exercise2220
