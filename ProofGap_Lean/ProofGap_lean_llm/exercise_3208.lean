import Mathlib

set_option linter.style.longLine false

noncomputable section

-- exercise: exercise_3208

def UniformConvergentOnSeq (F : ℕ -> ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ∃ H : ℝ -> ℝ, TendstoUniformlyOn F H Filter.atTop s

def Rect (a A b B : ℝ) : Set (ℝ × ℝ) := (Set.Icc a A) ×ˢ (Set.Icc b B)

theorem proof_gap_exercise_3208_1
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> (x, phi n x) ∈ Rect a A b B := by
  sorry

theorem proof_gap_exercise_3208_2
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h1 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> (x, phi n x) ∈ Rect a A b B)
  : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x) := by
  sorry

theorem proof_gap_exercise_3208_3
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h1 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> (x, phi n x) ∈ Rect a A b B)
  (h2 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  : UniformContinuousOn f (Rect a A b B) := by
  sorry

theorem proof_gap_exercise_3208_4
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h1 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> (x, phi n x) ∈ Rect a A b B)
  (h2 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (huc : UniformContinuousOn f (Rect a A b B))
  : ∀ eps > 0, ∃ delta > 0, ∀ x1 x2 y1 y2 : ℝ,
      (x1, y1) ∈ Rect a A b B -> (x2, y2) ∈ Rect a A b B ->
      |x1 - x2| < delta -> |y1 - y2| < delta ->
      |f (x1, y1) - f (x2, y2)| < eps := by
  sorry

theorem proof_gap_exercise_3208_5
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h1 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> (x, phi n x) ∈ Rect a A b B)
  (h2 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (huc : UniformContinuousOn f (Rect a A b B))
  (hdelta : ∀ eps > 0, ∃ delta > 0, ∀ x1 x2 y1 y2 : ℝ,
      (x1, y1) ∈ Rect a A b B -> (x2, y2) ∈ Rect a A b B ->
      |x1 - x2| < delta -> |y1 - y2| < delta ->
      |f (x1, y1) - f (x2, y2)| < eps)
  : ∀ eps > 0, ∃ delta > 0, ∀ y1 y2 : ℝ,
      y1 ∈ Set.Icc b B -> y2 ∈ Set.Icc b B -> |y1 - y2| < delta ->
      ∀ x : ℝ, x ∈ Set.Icc a A -> |f (x, y1) - f (x, y2)| < eps := by
  sorry

theorem proof_gap_exercise_3208_6
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h1 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> (x, phi n x) ∈ Rect a A b B)
  (h2 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (huc : UniformContinuousOn f (Rect a A b B))
  (hy : ∀ eps > 0, ∃ delta > 0, ∀ y1 y2 : ℝ,
      y1 ∈ Set.Icc b B -> y2 ∈ Set.Icc b B -> |y1 - y2| < delta ->
      ∀ x : ℝ, x ∈ Set.Icc a A -> |f (x, y1) - f (x, y2)| < eps)
  : ∀ eps > 0, ∃ delta > 0, ∃ N : ℕ, 0 < N ∧
      ∀ m n x, 0 < m -> 0 < n -> x ∈ Set.Icc a A -> m > N -> n > N ->
        |phi n x - phi m x| < delta := by
  sorry

theorem proof_gap_exercise_3208_7
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h1 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> (x, phi n x) ∈ Rect a A b B)
  (h2 : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (huc : UniformContinuousOn f (Rect a A b B))
  (h_cauchy_phi : ∀ eps > 0, ∃ delta > 0, ∃ N : ℕ, 0 < N ∧
      ∀ m n x, 0 < m -> 0 < n -> x ∈ Set.Icc a A -> m > N -> n > N ->
        |phi n x - phi m x| < delta)
  : ∀ eps > 0, ∃ N : ℕ, 0 < N ∧
      ∀ m n x, 0 < m -> 0 < n -> x ∈ Set.Icc a A -> m > N -> n > N ->
        |F n x - F m x| = |f (x, phi n x) - f (x, phi m x)| ∧
        |f (x, phi n x) - f (x, phi m x)| < eps := by
  sorry

theorem proof_gap_exercise_3208_8
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h_cauchy_F : ∀ eps > 0, ∃ N : ℕ, 0 < N ∧
      ∀ m n x, 0 < m -> 0 < n -> x ∈ Set.Icc a A -> m > N -> n > N ->
        |F n x - F m x| = |f (x, phi n x) - f (x, phi m x)| ∧
        |f (x, phi n x) - f (x, phi m x)| < eps)
  : UniformConvergentOnSeq F (Set.Icc a A) := by
  sorry

theorem proof_gap_exercise_3208_9
  (a A b B : ℝ) (f : ℝ × ℝ -> ℝ) (phi F : ℕ -> ℝ -> ℝ)
  (ha : a ≤ A) (hb : b ≤ B)
  (hf : ContinuousOn f (Rect a A b B))
  (hphi_conv : ∃ phi0 : ℝ -> ℝ, TendstoUniformlyOn phi phi0 Filter.atTop (Set.Icc a A))
  (hphi_range : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> b ≤ phi n x ∧ phi n x ≤ B)
  (hF : ∀ n x, 0 < n -> x ∈ Set.Icc a A -> F n x = f (x, phi n x))
  (h_final : UniformConvergentOnSeq F (Set.Icc a A))
  : UniformConvergentOnSeq F (Set.Icc a A) := by
  sorry

