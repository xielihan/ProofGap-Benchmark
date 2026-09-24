import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field

open scoped Topology

/-!
# Exercise 51

Semantic formalization of Exercise 51, gaps 1,2,3.
The source ellipsis is represented by a `Finset.range` sum.
-/

namespace ProofGap.Exercise51

noncomputable section

def u (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (k : ℝ) / (n : ℝ) ^ 2

def closed (n : ℕ) : ℝ :=
  (((n : ℝ) - 1) * (n : ℝ)) / (2 * (n : ℝ) ^ 2)

def SameLimit (a b : ℕ → ℝ) : Prop :=
  ∀ l : ℝ, Tendsto a atTop (𝓝 l) ↔ Tendsto b atTop (𝓝 l)

/-- Exercise 51, gap 1. -/
theorem gap1 :
    SameLimit u closed := by
  have heq : ∀ n, u n = closed n := by
    intro n
    by_cases hn : n = 0
    · subst n
      norm_num [u, closed]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hsum :
          (∑ k ∈ Finset.range n, (k : ℝ)) * 2 =
            (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
        have hcast := congrArg (fun m : ℕ => (m : ℝ))
          (Finset.sum_range_id_mul_two n)
        simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] at hcast
        exact hcast
      have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      unfold u closed
      rw [← Finset.sum_div]
      field_simp [hnreal]
      rw [hsub] at hsum
      nlinarith
  intro l
  exact Filter.tendsto_congr heq

/-- Exercise 51, gap 2. -/
theorem gap2
    (h1 : SameLimit u closed) :
    Tendsto closed atTop (𝓝 (1 / 2 : ℝ)) := by
  have hsmall :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)
  have hlim :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) / (n : ℝ))
        atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hsmall
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  unfold closed
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnreal]

/-- Exercise 51, gap 3. -/
theorem gap3
    (h1 : SameLimit u closed)
    (h2 : Tendsto closed atTop (𝓝 (1 / 2 : ℝ))) :
    Tendsto u atTop (𝓝 (1 / 2 : ℝ)) := by
  exact (h1 (1 / 2)).mpr h2

end

end ProofGap.Exercise51
