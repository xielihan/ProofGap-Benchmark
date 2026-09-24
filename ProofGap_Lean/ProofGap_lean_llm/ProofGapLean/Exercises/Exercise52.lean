import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology

/-!
# Exercise 52

Semantic formalization of Exercise 52, gaps 1,...,9.
All alternating sums hidden by source ellipses are explicit finite sums.
-/

namespace ProofGap.Exercise52

noncomputable section

def u (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    (-1 : ℝ) ^ (i - 1) * (i : ℝ) / (n : ℝ)

def evenExpansion (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (2 * k),
    (-1 : ℝ) ^ (i - 1) * (i : ℝ) / (2 * k : ℕ)

def oddExpansion (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (2 * k + 1),
    (-1 : ℝ) ^ (i - 1) * (i : ℝ) / (2 * k + 1 : ℕ)

def evenClosed (k : ℕ) : ℝ :=
  -(k : ℝ) / (2 * k : ℕ)

def oddClosed (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) / (2 * (k : ℝ) + 1)

private def altTerm (i : ℕ) : ℝ :=
  (-1 : ℝ) ^ (i - 1) * (i : ℝ)

private theorem alternating_sums (k : ℕ) :
    (∑ i ∈ Finset.Icc 1 (2 * k), altTerm i) = -(k : ℝ) ∧
      (∑ i ∈ Finset.Icc 1 (2 * k + 1), altTerm i) = (k : ℝ) + 1 := by
  induction k with
  | zero =>
      norm_num [altTerm]
  | succ k ih =>
      have heven :
          (∑ i ∈ Finset.Icc 1 (2 * (k + 1)), altTerm i) =
            -((k + 1 : ℕ) : ℝ) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          Finset.sum_Icc_succ_top (by omega), ih.2]
        simp [altTerm, show (2 * k + 2) - 1 = 2 * k + 1 by omega,
          pow_succ, pow_mul]
        ring
      refine ⟨heven, ?_⟩
      rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega), heven]
      simp [altTerm, show (2 * (k + 1) + 1) - 1 = 2 * (k + 1) by omega,
        pow_mul]
      ring

/-- Exercise 52, gap 1. -/
theorem gap1 :
    ∀ n k : ℕ, n = 2 * k → u n = evenExpansion k := by
  intro n k hnk
  subst n
  rfl

/-- Exercise 52, gap 2; positive `k` is restored. -/
theorem gap2
    (h1 : ∀ n k : ℕ, n = 2 * k → u n = evenExpansion k) :
    ∀ n k : ℕ, 0 < k → n = 2 * k →
      evenExpansion k = evenClosed k := by
  intro n k hk hnk
  unfold evenExpansion evenClosed
  change
    (∑ i ∈ Finset.Icc 1 (2 * k), altTerm i / ((2 * k : ℕ) : ℝ)) =
      -(k : ℝ) / ((2 * k : ℕ) : ℝ)
  rw [← Finset.sum_div, (alternating_sums k).1]

/-- Exercise 52, gap 3; positive `k` is restored. -/
theorem gap3
    (h2 : ∀ n k : ℕ, 0 < k → n = 2 * k →
      evenExpansion k = evenClosed k) :
    ∀ n k : ℕ, 0 < k → n = 2 * k →
      evenClosed k = -(1 / 2 : ℝ) := by
  intro n k hk hnk
  unfold evenClosed
  have hkreal : (k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  norm_num
  field_simp [hkreal]

/-- Exercise 52, gap 4; positive `k` is restored. -/
theorem gap4
    (h1 : ∀ n k : ℕ, n = 2 * k → u n = evenExpansion k)
    (h2 : ∀ n k : ℕ, 0 < k → n = 2 * k →
      evenExpansion k = evenClosed k)
    (h3 : ∀ n k : ℕ, 0 < k → n = 2 * k →
      evenClosed k = -(1 / 2 : ℝ)) :
    ∀ n k : ℕ, 0 < k → n = 2 * k →
      u n = -(1 / 2 : ℝ) := by
  intro n k hk hnk
  exact (h1 n k hnk).trans
    ((h2 n k hk hnk).trans (h3 n k hk hnk))

/-- Exercise 52, gap 5. -/
theorem gap5 :
    ∀ n k : ℕ, n = 2 * k + 1 → u n = oddExpansion k := by
  intro n k hnk
  subst n
  rfl

/-- Exercise 52, gap 6. -/
theorem gap6
    (h5 : ∀ n k : ℕ, n = 2 * k + 1 → u n = oddExpansion k) :
    ∀ n k : ℕ, n = 2 * k + 1 →
      oddExpansion k = oddClosed k := by
  intro n k hnk
  unfold oddExpansion oddClosed
  change
    (∑ i ∈ Finset.Icc 1 (2 * k + 1),
      altTerm i / ((2 * k + 1 : ℕ) : ℝ)) =
        ((k : ℝ) + 1) / (2 * (k : ℝ) + 1)
  rw [← Finset.sum_div, (alternating_sums k).2]
  norm_num

/-- Exercise 52, gap 7. -/
theorem gap7
    (h5 : ∀ n k : ℕ, n = 2 * k + 1 → u n = oddExpansion k)
    (h6 : ∀ n k : ℕ, n = 2 * k + 1 →
      oddExpansion k = oddClosed k) :
    ∀ n k : ℕ, n = 2 * k + 1 → u n = oddClosed k := by
  intro n k hnk
  exact (h5 n k hnk).trans (h6 n k hnk)

/-- Exercise 52, gap 8; irrelevant `n,k` binders are removed. -/
theorem gap8
    (h7 : ∀ n k : ℕ, n = 2 * k + 1 → u n = oddClosed k) :
    Tendsto oddClosed atTop (𝓝 (1 / 2 : ℝ)) := by
  have ht :=
    tendsto_add_mul_div_add_mul_atTop_nhds
      (1 : ℝ) 1 1 (d := 2) (by norm_num)
  apply Filter.Tendsto.congr' _ ht
  exact Filter.Eventually.of_forall fun k => by
    unfold oddClosed
    congr 1 <;> ring

/-- Exercise 52, gap 9. -/
theorem gap9
    (h4 : ∀ n k : ℕ, 0 < k → n = 2 * k →
      u n = -(1 / 2 : ℝ))
    (h7 : ∀ n k : ℕ, n = 2 * k + 1 → u n = oddClosed k)
    (h8 : Tendsto oddClosed atTop (𝓝 (1 / 2 : ℝ))) :
    ¬ ∃ L : ℝ, Tendsto u atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hevenMap : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    omega
  have hoddMap : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    omega
  have hLeven :
      Tendsto (fun k : ℕ => u (2 * k)) atTop (𝓝 L) :=
    hL.comp hevenMap
  have heven :
      Tendsto (fun k : ℕ => u (2 * k)) atTop (𝓝 (-(1 / 2 : ℝ))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    exact (h4 (2 * k) k hk rfl).symm
  have hLodd :
      Tendsto (fun k : ℕ => u (2 * k + 1)) atTop (𝓝 L) :=
    hL.comp hoddMap
  have hodd :
      Tendsto (fun k : ℕ => u (2 * k + 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
    apply Filter.Tendsto.congr' _ h8
    exact Filter.Eventually.of_forall fun k => (h7 (2 * k + 1) k rfl).symm
  have hneg : L = -(1 / 2 : ℝ) :=
    tendsto_nhds_unique hLeven heven
  have hpos : L = (1 / 2 : ℝ) :=
    tendsto_nhds_unique hLodd hodd
  linarith

end

end ProofGap.Exercise52
