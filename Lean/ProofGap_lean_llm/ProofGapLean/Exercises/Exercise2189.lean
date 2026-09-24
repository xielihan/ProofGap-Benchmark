import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2189
noncomputable section

open Filter
open scoped BigOperators Interval

def IsPartition (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, x i < x (i + 1)

def sumFor (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (1 / (x i * x (i + 1))) * (x (i + 1) - x i)

private theorem partition_pos (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x)
    {i : ℕ} (hi : i ≤ n) : 0 < x i := by
  have h : ∀ j : ℕ, j ≤ n → 0 < x j := by
    intro j
    induction j with
    | zero =>
        intro hj
        rw [hp.1]
        exact hab.1
    | succ j ih =>
        intro hj
        have hjn : j < n := Nat.lt_of_succ_le hj
        have hprev : 0 < x j :=
          ih (Nat.le_trans (Nat.le_succ j) hj)
        exact lt_trans hprev (hp.2.2 j hjn)
  exact h i hi

theorem gap1 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) :
    a = x 0 := by
  exact hp.1.symm

theorem gap2 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) (hn : 1 ≤ n) :
    x 0 < x 1 := by
  exact hp.2.2 0 hn

theorem gap3 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) (hn : 2 ≤ n) :
    x 1 < x 2 := by
  exact hp.2.2 1 hn

theorem gap4 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) :
    ∀ i < n, x i < x (i + 1) := by
  exact hp.2.2

theorem gap5 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) (hn : 0 < n) :
    x (n - 1) < x n := by
  have hlt : n - 1 < n := Nat.sub_lt hn Nat.zero_lt_one
  have hstep := hp.2.2 (n - 1) hlt
  simpa [Nat.sub_add_cancel hn] using hstep

theorem gap6 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) :
    x n = b := by
  exact hp.2.1

theorem gap7 (a b : ℝ) (hab : 0 < a ∧ a < b) :
    a < b := by
  exact hab.2

theorem gap8 (a b : ℝ) (n : ℕ) (x ξ : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x)
    (hξ : ∀ i < n, ξ i ∈ Set.Icc (x i) (x (i + 1))) :
    ∀ i < n, ξ i ∈ Set.Icc (x i) (x (i + 1)) := by
  exact hξ

theorem gap9 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) :
    sumFor x n =
      ∑ i ∈ Finset.range n,
        (1 / (x i * x (i + 1))) * (x (i + 1) - x i) := by
  rfl

theorem gap10 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) :
    (∑ i ∈ Finset.range n,
        (1 / (x i * x (i + 1))) * (x (i + 1) - x i)) =
      ∑ i ∈ Finset.range n, (1 / x i - 1 / x (i + 1)) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hxi : x i ≠ 0 :=
    ne_of_gt (partition_pos a b n x hab hp (i := i) (Nat.le_of_lt hin))
  have hxi1 : x (i + 1) ≠ 0 :=
    ne_of_gt (partition_pos a b n x hab hp (i := i + 1) (Nat.succ_le_iff.mpr hin))
  field_simp [hxi, hxi1] <;> ring

theorem gap11 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) :
    (∑ i ∈ Finset.range n, (1 / x i - 1 / x (i + 1))) =
      1 / a - 1 / b := by
  have htel : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, (1 / x i - 1 / x (i + 1))) =
        1 / x 0 - 1 / x m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  simpa [hp.1, hp.2.1] using htel n

theorem gap12 (a b : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hab : 0 < a ∧ a < b) (hp : IsPartition a b n x) :
    sumFor x n = 1 / a - 1 / b := by
  calc
    sumFor x n =
        ∑ i ∈ Finset.range n,
          (1 / (x i * x (i + 1))) * (x (i + 1) - x i) :=
      gap9 a b n x hab hp
    _ = ∑ i ∈ Finset.range n, (1 / x i - 1 / x (i + 1)) :=
      gap10 a b n x hab hp
    _ = 1 / a - 1 / b := gap11 a b n x hab hp

theorem gap13 (a b : ℝ) (x : ℕ → ℕ → ℝ)
    (hab : 0 < a ∧ a < b)
    (hp : ∀ n, 0 < n → IsPartition a b n (x n)) :
    Tendsto (fun n => sumFor (x n) n) atTop (nhds (1 / a - 1 / b)) := by
  have heq :
      (fun n => sumFor (x n) n) =ᶠ[atTop]
        (fun _ : ℕ => 1 / a - 1 / b) :=
    (eventually_gt_atTop 0).mono fun n hn =>
      gap12 a b n (x n) hab (hp n hn)
  rw [tendsto_congr' heq]
  exact tendsto_const_nhds

theorem gap14 (a b : ℝ) (hab : 0 < a ∧ a < b) :
    (∫ x in a..b, 1 / x ^ 2) = 1 / a - 1 / b := by
  have hpos : ∀ y ∈ Set.uIcc a b, 0 < y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le (le_of_lt hab.2)] using hy
    exact lt_of_lt_of_le hab.1 hyIcc.1
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun z : ℝ => -(z⁻¹)) (1 / y ^ 2) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (hpos y hy)
    convert ((hasDerivAt_id y).inv hy0).neg using 1 <;> simp <;> ring
  have hcont : ContinuousOn (fun y : ℝ => 1 / y ^ 2) (Set.uIcc a b) := by
    exact continuousOn_const.div (continuousOn_id.pow 2) fun y hy =>
      pow_ne_zero 2 (ne_of_gt (hpos y hy))
  calc
    (∫ y in a..b, 1 / y ^ 2) = (-(b⁻¹)) - (-(a⁻¹)) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    _ = 1 / a - 1 / b := by ring

end
end ProofGap.Exercise2189
