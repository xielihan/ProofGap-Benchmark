import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2567_2

theorem gap1
    (a b : ℕ → ℝ)
    (haDiv : ¬ Summable a) (hbDiv : ¬ Summable b)
    (haNonneg : ∀ n, 0 ≤ a n) (hbNonneg : ∀ n, 0 ≤ b n) :
    ∀ n, max (a n) (b n) ≥ a n := by
  intro n
  exact le_max_left (a n) (b n)

theorem gap2
    (a b : ℕ → ℝ)
    (haDiv : ¬ Summable a) (hbDiv : ¬ Summable b)
    (haNonneg : ∀ n, 0 ≤ a n) (hbNonneg : ∀ n, 0 ≤ b n)
    (hmax : ∀ n, max (a n) (b n) ≥ a n) :
    ∀ n, a n ≥ 0 := by
  intro n
  exact haNonneg n

theorem gap3
    (a b : ℕ → ℝ)
    (haDiv : ¬ Summable a) (hbDiv : ¬ Summable b)
    (haNonneg : ∀ n, 0 ≤ a n) (hbNonneg : ∀ n, 0 ≤ b n)
    (hmax : ∀ n, max (a n) (b n) ≥ a n)
    (haPos : ∀ n, a n ≥ 0) :
    ∀ n, max (a n) (b n) ≥ 0 := by
  intro n
  exact le_trans (haPos n) (hmax n)

theorem gap4
    (a b : ℕ → ℝ)
    (haDiv : ¬ Summable a) (hbDiv : ¬ Summable b)
    (haNonneg : ∀ n, 0 ≤ a n) (hbNonneg : ∀ n, 0 ≤ b n)
    (hmax : ∀ n, max (a n) (b n) ≥ a n)
    (hmaxPos : ∀ n, max (a n) (b n) ≥ 0) :
    ¬ Summable (fun n => max (a n) (b n)) := by
  intro hsum
  apply haDiv
  exact Summable.of_nonneg_of_le haNonneg hmax hsum

theorem gap5
    (a b : ℕ → ℝ)
    (haDiv : ¬ Summable a) (hbDiv : ¬ Summable b)
    (haNonneg : ∀ n, 0 ≤ a n) (hbNonneg : ∀ n, 0 ≤ b n)
    (hresult : ¬ Summable (fun n => max (a n) (b n))) :
    ¬ Summable (fun n => max (a n) (b n)) := by
  exact hresult

end ProofGap.Exercise2567_2
