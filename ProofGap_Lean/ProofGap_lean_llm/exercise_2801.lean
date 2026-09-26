import Mathlib

set_option linter.style.longLine false

noncomputable section

open Filter
open scoped Topology

namespace ProofGapBatch5

def seqLimitValue (u : ℕ → ℝ) : ℝ :=
  limUnder atTop u

def derivativeSeq (f : ℕ × ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  deriv (fun t : ℝ => f (n, t)) x

def divergentSeq (u : ℕ → ℝ) : Prop :=
  ¬ ∃ L : ℝ, Tendsto u atTop (𝓝 L)

def wholeRealLine : Set ℝ :=
  {x : ℝ | ∃ y : ℝ, x = y}

namespace exercise_2801

theorem proof_gap_exercise_2801_1
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2))) :
    ∀ x : ℝ, Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 (x ^ 2)) := by
  sorry

theorem proof_gap_exercise_2801_2
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hlim : ∀ x : ℝ, Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 (x ^ 2))) :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      |f (n, x) - x ^ 2| =
        |(1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2))| ∧
      |(1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2))| ≤ 1 / (n : ℝ) := by
  sorry

theorem proof_gap_exercise_2801_3
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hlim : ∀ x : ℝ, Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 (x ^ 2)))
    (hbound : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      |f (n, x) - x ^ 2| =
        |(1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2))| ∧
      |(1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2))| ≤ 1 / (n : ℝ)) :
    ∀ N : ℝ → ℕ, ∀ n : ℕ, ∀ x : ℝ, ∀ ε : ℝ,
      0 < ε → N ε = Nat.floor (1 / ε) → n > N ε → |f (n, x) - x ^ 2| < ε := by
  sorry

theorem proof_gap_exercise_2801_4
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hlim : ∀ x : ℝ, Tendsto (fun n : ℕ => f (n, x)) atTop (𝓝 (x ^ 2)))
    (hbound : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      |f (n, x) - x ^ 2| =
        |(1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2))| ∧
      |(1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2))| ≤ 1 / (n : ℝ))
    (heps : ∀ N : ℝ → ℕ, ∀ n : ℕ, ∀ x : ℝ, ∀ ε : ℝ,
      0 < ε → N ε = Nat.floor (1 / ε) → n > N ε → |f (n, x) - x ^ 2| < ε) :
    TendstoUniformlyOn (fun n x => f (n, x)) (fun x : ℝ => x ^ 2) atTop wholeRealLine := by
  sorry

theorem proof_gap_exercise_2801_5
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hunif : TendstoUniformlyOn (fun n x => f (n, x)) (fun x : ℝ => x ^ 2) atTop wholeRealLine) :
    (fun x : ℝ => deriv (fun y : ℝ => seqLimitValue (fun n : ℕ => f (n, y))) x) =
      (fun x : ℝ => 2 * x) := by
  sorry

theorem proof_gap_exercise_2801_6
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hlimit_deriv : (fun x : ℝ => deriv (fun y : ℝ => seqLimitValue (fun n : ℕ => f (n, y))) x) =
      (fun x : ℝ => 2 * x)) :
    ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      derivativeSeq f n x = 2 * x + Real.cos ((n : ℝ) * (x + Real.pi / 2)) := by
  sorry

theorem proof_gap_exercise_2801_7
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hderiv : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      derivativeSeq f n x = 2 * x + Real.cos ((n : ℝ) * (x + Real.pi / 2))) :
    ∀ x : ℝ, divergentSeq (fun n : ℕ => derivativeSeq f n x) := by
  sorry

theorem proof_gap_exercise_2801_8
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hdiv : ∀ x : ℝ, divergentSeq (fun n : ℕ => derivativeSeq f n x)) :
    (fun x : ℝ => deriv (fun y : ℝ => seqLimitValue (fun n : ℕ => f (n, y))) x) ≠
      (fun x : ℝ => seqLimitValue (fun n : ℕ => derivativeSeq f n x)) := by
  sorry

theorem proof_gap_exercise_2801_9
    (f : ℕ × ℝ → ℝ)
    (hf : ∀ n : ℕ, 0 < n → ∀ x : ℝ,
      f (n, x) = x ^ 2 + (1 / (n : ℝ)) * Real.sin ((n : ℝ) * (x + Real.pi / 2)))
    (hunif : TendstoUniformlyOn (fun n x => f (n, x)) (fun x : ℝ => x ^ 2) atTop wholeRealLine)
    (hne : (fun x : ℝ => deriv (fun y : ℝ => seqLimitValue (fun n : ℕ => f (n, y))) x) ≠
      (fun x : ℝ => seqLimitValue (fun n : ℕ => derivativeSeq f n x))) :
    TendstoUniformlyOn (fun n x => f (n, x)) (fun x : ℝ => x ^ 2) atTop wholeRealLine ∧
      (fun x : ℝ => deriv (fun y : ℝ => seqLimitValue (fun n : ℕ => f (n, y))) x) ≠
        (fun x : ℝ => seqLimitValue (fun n : ℕ => derivativeSeq f n x)) := by
  sorry

end exercise_2801

end ProofGapBatch5
