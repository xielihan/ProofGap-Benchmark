import Mathlib

/- All eight source gaps are retained, including the shadowed existential k in gap 3.
The source Markdown omits absolute values in its conclusion; the supplied gaps
explicitly contain them. See reviews/exercise_126.json for this source discrepancy.
IsSeq(x) is exactly the declared type ℕ → ℝ (the theorem library).
IsSubseqIndexFunc(p) is ℕ → ℕ together with StrictMono p.
-/
namespace Exercise126

/-- Boundedness of the actual restriction to s, with no extension off s. -/
def BoundedOn (x : ℕ → ℝ) (s : Set ℕ) : Prop :=
  ∃ M : ℝ, ∀ n : ℕ, n ∈ s → |x n| ≤ M

-- Exercise 126, gap 1
theorem proof_gap_exercise_126_1
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1 := by
  sorry

-- Exercise 126, gap 2
theorem proof_gap_exercise_126_2
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  (h4 : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1)
  : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → ¬ BoundedOn x {n : ℕ | 0 < n ∧ n > p k} := by
  sorry

-- Exercise 126, gap 3
theorem proof_gap_exercise_126_3
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  (h4 : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1)
  (h5 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → ¬ BoundedOn x {n : ℕ | 0 < n ∧ n > p k})
  : ∀ k_outer : ℕ, 0 < k_outer → ∃ (p : ℕ → ℕ) (k_inner : ℕ),
      0 < p (k_inner + 1) ∧ p (k_inner + 1) > p k_inner ∧
      |x (p (k_inner + 1))| > (k_inner : ℝ) + 1 := by
  sorry

-- Exercise 126, gap 4
theorem proof_gap_exercise_126_4
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  (h4 : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1)
  (h5 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → ¬ BoundedOn x {n : ℕ | 0 < n ∧ n > p k})
  (h6 : ∀ k_outer : ℕ, 0 < k_outer → ∃ (p : ℕ → ℕ) (k_inner : ℕ),
      0 < p (k_inner + 1) ∧ p (k_inner + 1) > p k_inner ∧
      |x (p (k_inner + 1))| > (k_inner : ℝ) + 1)
  : ∃ p : ℕ → ℕ, StrictMono p := by
  sorry

-- Exercise 126, gap 5
theorem proof_gap_exercise_126_5
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  (h4 : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1)
  (h5 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → ¬ BoundedOn x {n : ℕ | 0 < n ∧ n > p k})
  (h6 : ∀ k_outer : ℕ, 0 < k_outer → ∃ (p : ℕ → ℕ) (k_inner : ℕ),
      0 < p (k_inner + 1) ∧ p (k_inner + 1) > p k_inner ∧
      |x (p (k_inner + 1))| > (k_inner : ℝ) + 1)
  (h7 : ∃ p : ℕ → ℕ, StrictMono p)
  : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → |x (p k)| > (k : ℝ) := by
  sorry

-- Exercise 126, gap 6
theorem proof_gap_exercise_126_6
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  (h4 : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1)
  (h5 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → ¬ BoundedOn x {n : ℕ | 0 < n ∧ n > p k})
  (h6 : ∀ k_outer : ℕ, 0 < k_outer → ∃ (p : ℕ → ℕ) (k_inner : ℕ),
      0 < p (k_inner + 1) ∧ p (k_inner + 1) > p k_inner ∧
      |x (p (k_inner + 1))| > (k_inner : ℝ) + 1)
  (h7 : ∃ p : ℕ → ℕ, StrictMono p)
  (h8 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → |x (p k)| > (k : ℝ))
  : ∃ p : ℕ → ℕ, Filter.Tendsto (fun k : ℕ => |x (p k)|) Filter.atTop Filter.atTop := by
  sorry

-- Exercise 126, gap 7
theorem proof_gap_exercise_126_7
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  (h4 : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1)
  (h5 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → ¬ BoundedOn x {n : ℕ | 0 < n ∧ n > p k})
  (h6 : ∀ k_outer : ℕ, 0 < k_outer → ∃ (p : ℕ → ℕ) (k_inner : ℕ),
      0 < p (k_inner + 1) ∧ p (k_inner + 1) > p k_inner ∧
      |x (p (k_inner + 1))| > (k_inner : ℝ) + 1)
  (h7 : ∃ p : ℕ → ℕ, StrictMono p)
  (h8 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → |x (p k)| > (k : ℝ))
  (h9 : ∃ p : ℕ → ℕ, Filter.Tendsto (fun k : ℕ => |x (p k)|) Filter.atTop Filter.atTop)
  : ∃ p : ℕ → ℕ, StrictMono p ∧
      Filter.Tendsto (fun k : ℕ => |x (p k)|) Filter.atTop Filter.atTop := by
  sorry

-- Exercise 126, gap 8
theorem proof_gap_exercise_126_8
  (x : ℕ → ℝ)
  (h_unbounded : ¬ BoundedOn x Set.univ)
  (h4 : ∃ p : ℕ → ℕ, 0 < p 1 ∧ |x (p 1)| > 1)
  (h5 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → ¬ BoundedOn x {n : ℕ | 0 < n ∧ n > p k})
  (h6 : ∀ k_outer : ℕ, 0 < k_outer → ∃ (p : ℕ → ℕ) (k_inner : ℕ),
      0 < p (k_inner + 1) ∧ p (k_inner + 1) > p k_inner ∧
      |x (p (k_inner + 1))| > (k_inner : ℝ) + 1)
  (h7 : ∃ p : ℕ → ℕ, StrictMono p)
  (h8 : ∃ p : ℕ → ℕ, ∀ k : ℕ, 0 < k → |x (p k)| > (k : ℝ))
  (h9 : ∃ p : ℕ → ℕ, Filter.Tendsto (fun k : ℕ => |x (p k)|) Filter.atTop Filter.atTop)
  (h10 : ∃ p : ℕ → ℕ, StrictMono p ∧
      Filter.Tendsto (fun k : ℕ => |x (p k)|) Filter.atTop Filter.atTop)
  : ∃ p : ℕ → ℕ, StrictMono p ∧
      Filter.Tendsto (fun k : ℕ => |x (p k)|) Filter.atTop Filter.atTop := by
  sorry

end Exercise126
