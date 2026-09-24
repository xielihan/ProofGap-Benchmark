import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2702

noncomputable section

open Filter
open scoped BigOperators

def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

def absolutePartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, |a i|

def positivePartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (|a i| + a i) / 2

def negativePartialSum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (|a i| - a i) / 2

def ConditionallySummable (a : ℕ → ℝ) : Prop :=
  Summable a ∧ ¬ Summable (fun n => |a n|)

private theorem absolutePartialSum_tendsto_atTop_of_conditionallySummable
    (a : ℕ → ℝ) (h : ConditionallySummable a) :
    Tendsto (absolutePartialSum a) atTop atTop := by
  simpa [absolutePartialSum] using
    ((not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => abs_nonneg (a n))).1 h.2)

theorem gap1 (a : ℕ → ℝ) (h : ConditionallySummable a) :
    Summable a := by
  exact h.1

theorem gap2 (a : ℕ → ℝ) (h : ConditionallySummable a) :
    ¬ Summable (fun n => |a n|) := by
  exact h.2

theorem gap3 (a : ℕ → ℝ) :
    ∀ n : ℕ,
      negativePartialSum a n / positivePartialSum a n =
        (absolutePartialSum a n - partialSum a n) /
          (absolutePartialSum a n + partialSum a n) := by
  intro n
  have hneg :
      negativePartialSum a n =
        (absolutePartialSum a n - partialSum a n) / 2 := by
    unfold negativePartialSum absolutePartialSum partialSum
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hpos :
      positivePartialSum a n =
        (absolutePartialSum a n + partialSum a n) / 2 := by
    unfold positivePartialSum absolutePartialSum partialSum
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hneg, hpos]
  by_cases hzero : absolutePartialSum a n + partialSum a n = 0
  · rw [hzero]
    norm_num
  · field_simp [hzero] <;> ring

theorem gap4 (a : ℕ → ℝ) :
    ∀ n : ℕ, absolutePartialSum a n ≠ 0 →
      (absolutePartialSum a n - partialSum a n) /
          (absolutePartialSum a n + partialSum a n) =
        (1 - partialSum a n / absolutePartialSum a n) /
          (1 + partialSum a n / absolutePartialSum a n) := by
  intro n hA
  set A : ℝ := absolutePartialSum a n
  set S : ℝ := partialSum a n
  change (A - S) / (A + S) = (1 - S / A) / (1 + S / A)
  have hA' : A ≠ 0 := by
    simpa [A] using hA
  by_cases hAS : A + S = 0
  · have hS : S = -A := by
      linarith
    rw [hAS, hS]
    simp [hA']
  · field_simp [hA', hAS] <;> ring

theorem gap5 (a : ℕ → ℝ) :
    ∀ n : ℕ, absolutePartialSum a n ≠ 0 →
      negativePartialSum a n / positivePartialSum a n =
        (1 - partialSum a n / absolutePartialSum a n) /
          (1 + partialSum a n / absolutePartialSum a n) := by
  intro n hn
  calc
    negativePartialSum a n / positivePartialSum a n =
        (absolutePartialSum a n - partialSum a n) /
          (absolutePartialSum a n + partialSum a n) := gap3 a n
    _ = (1 - partialSum a n / absolutePartialSum a n) /
          (1 + partialSum a n / absolutePartialSum a n) := gap4 a n hn

theorem gap6 (a : ℕ → ℝ) (h : ConditionallySummable a) :
    Tendsto
      (fun n : ℕ => partialSum a n / absolutePartialSum a n)
      atTop (nhds 0) := by
  have hpartial :
      Tendsto (partialSum a) atTop (nhds (∑' n, a n)) := by
    simpa [partialSum] using h.1.hasSum.tendsto_sum_nat
  have hinverse :
      Tendsto (fun n : ℕ => (absolutePartialSum a n)⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (absolutePartialSum_tendsto_atTop_of_conditionallySummable a h)
  simpa [div_eq_mul_inv] using hpartial.mul hinverse

theorem gap7 (a : ℕ → ℝ) (h : ConditionallySummable a) :
    Tendsto
      (fun n : ℕ => negativePartialSum a n / positivePartialSum a n)
      atTop (nhds 1) := by
  have habsolute :=
    absolutePartialSum_tendsto_atTop_of_conditionallySummable a h
  have hpositive :
      ∀ᶠ n : ℕ in atTop, 0 < absolutePartialSum a n :=
    habsolute (eventually_gt_atTop (0 : ℝ))
  have hzero := gap6 a h
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have htransform :
      Tendsto
        (fun n : ℕ =>
          (1 - partialSum a n / absolutePartialSum a n) /
            (1 + partialSum a n / absolutePartialSum a n))
        atTop (nhds 1) := by
    simpa using
      ((hone.sub hzero).div (hone.add hzero)
        (by norm_num : (1 : ℝ) + 0 ≠ 0))
  exact htransform.congr' (by
    filter_upwards [hpositive] with n hn
    exact (gap5 a n (ne_of_gt hn)).symm)

theorem gap8 (a : ℕ → ℝ) (h : ConditionallySummable a) :
    Tendsto
      (fun n : ℕ => negativePartialSum a n / positivePartialSum a n)
      atTop (nhds 1) := by
  exact gap7 a h

end

end ProofGap.Exercise2702
