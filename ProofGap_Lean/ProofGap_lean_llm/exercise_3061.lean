import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConvergentSeq (u : ℕ -> ℝ) : Prop :=
  ∃ l : ℝ, Tendsto u atTop (𝓝 l)

noncomputable def infiniteProductFrom (a : ℕ -> ℝ) (start : ℕ) (L : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (Finset.Icc start N).prod (fun k => a k)) atTop (𝓝 L)

-- exercise: exercise_3061

-- GAP 1: rewrite each factor by factoring k^2 - 4 and k^2 - 1.
theorem proof_gap_exercise_3061_1
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, 3 ≤ n -> P n = (Finset.Icc 3 n).prod (fun k => (((k : ℝ) ^ 2 - 4) /. ((k : ℝ) ^ 2 - 1))))
  : ∀ n : ℕ, 3 ≤ n -> P n =
      (Finset.Icc 3 n).prod (fun k => ((((k : ℝ) - 2) * ((k : ℝ) + 2)) /. (((k : ℝ) - 1) * ((k : ℝ) + 1)))) := by
  sorry

-- GAP 2: telescope the rewritten finite product.
theorem proof_gap_exercise_3061_2
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, 3 ≤ n -> P n = (Finset.Icc 3 n).prod (fun k => (((k : ℝ) ^ 2 - 4) /. ((k : ℝ) ^ 2 - 1))))
  (h1 : ∀ n : ℕ, 3 ≤ n -> P n =
      (Finset.Icc 3 n).prod (fun k => ((((k : ℝ) - 2) * ((k : ℝ) + 2)) /. (((k : ℝ) - 1) * ((k : ℝ) + 1)))))
  : ∀ n : ℕ, 3 ≤ n -> P n = ((n : ℝ) + 2) /. (4 * ((n : ℝ) - 1)) := by
  sorry

-- GAP 3: limit of the closed-form partial products.
theorem proof_gap_exercise_3061_3
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, 3 ≤ n -> P n = (Finset.Icc 3 n).prod (fun k => (((k : ℝ) ^ 2 - 4) /. ((k : ℝ) ^ 2 - 1))))
  (h1 : ∀ n : ℕ, 3 ≤ n -> P n =
      (Finset.Icc 3 n).prod (fun k => ((((k : ℝ) - 2) * ((k : ℝ) + 2)) /. (((k : ℝ) - 1) * ((k : ℝ) + 1)))))
  (h2 : ∀ n : ℕ, 3 ≤ n -> P n = ((n : ℝ) + 2) /. (4 * ((n : ℝ) - 1)))
  : Tendsto (fun n : ℕ => ((n : ℝ) + 2) /. (4 * ((n : ℝ) - 1))) atTop (𝓝 (1 /. 4)) := by
  sorry

-- GAP 4: convergence of the partial-product sequence.
theorem proof_gap_exercise_3061_4
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, 3 ≤ n -> P n = (Finset.Icc 3 n).prod (fun k => (((k : ℝ) ^ 2 - 4) /. ((k : ℝ) ^ 2 - 1))))
  (h1 : ∀ n : ℕ, 3 ≤ n -> P n =
      (Finset.Icc 3 n).prod (fun k => ((((k : ℝ) - 2) * ((k : ℝ) + 2)) /. (((k : ℝ) - 1) * ((k : ℝ) + 1)))))
  (h2 : ∀ n : ℕ, 3 ≤ n -> P n = ((n : ℝ) + 2) /. (4 * ((n : ℝ) - 1)))
  (h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 2) /. (4 * ((n : ℝ) - 1))) atTop (𝓝 (1 /. 4)))
  : ConvergentSeq P := by
  sorry

-- GAP 5: final value of the infinite product.
theorem proof_gap_exercise_3061_5
  (P : ℕ -> ℝ)
  (hP : ∀ n : ℕ, 3 ≤ n -> P n = (Finset.Icc 3 n).prod (fun k => (((k : ℝ) ^ 2 - 4) /. ((k : ℝ) ^ 2 - 1))))
  (h1 : ∀ n : ℕ, 3 ≤ n -> P n =
      (Finset.Icc 3 n).prod (fun k => ((((k : ℝ) - 2) * ((k : ℝ) + 2)) /. (((k : ℝ) - 1) * ((k : ℝ) + 1)))))
  (h2 : ∀ n : ℕ, 3 ≤ n -> P n = ((n : ℝ) + 2) /. (4 * ((n : ℝ) - 1)))
  (h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 2) /. (4 * ((n : ℝ) - 1))) atTop (𝓝 (1 /. 4)))
  (h4 : ConvergentSeq P)
  : infiniteProductFrom (fun n : ℕ => (((n : ℝ) ^ 2 - 4) /. ((n : ℝ) ^ 2 - 1))) 3 (1 /. 4) := by
  sorry
