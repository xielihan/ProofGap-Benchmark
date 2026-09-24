import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology
open Filter

def lpContinuousOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop := ContinuousOn f s
def lpUniformContinuousOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop := UniformContinuousOn f s
def lpUniformConvergentOn (G : ℕ × ℝ -> ℝ) (s : Set ℝ) (F : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n > N -> ∀ x : ℝ, x ∈ s -> |F x - G (n, x)| < ε
noncomputable def lpIntegralLimit (f : ℝ -> ℝ) : ℝ -> ℝ := fun x => ∫ t in x..(x + 1), f t
def lpPointwiseLimit (F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ 0 < n -> Tendsto (fun m : ℕ => G (m, x)) atTop (𝓝 (F x))
def lpRiemannSplit (f F : ℝ -> ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ 0 < n -> F x = ∑ i ∈ Finset.range n, ∫ t in (x + (i : ℝ) / n)..(x + ((i + 1 : ℕ) : ℝ) / n), f t
def lpThetaIntegralFormula (f : ℝ -> ℝ) (n : ℕ) (x : ℝ) : Prop :=
  ∃ θ : ℕ -> ℝ, ∀ i : ℕ, i ∈ (Set.univ : Set ℕ) ∧ i < n -> 0 < θ i ∧ θ i < 1 ∧ (∫ t in (x + (i : ℝ) / n)..(x + ((i + 1 : ℕ) : ℝ) / n), f t) = (1 / (n : ℝ)) * f (x + (i : ℝ) / n + θ i / (n : ℝ))
def lpThetaIntervalControl (n : ℕ) (a b : ℝ) (θ : ℕ -> ℝ) : Prop :=
  ∀ (x aq bq : ℝ) (i : ℕ), x ∈ (Set.univ : Set ℝ) ∧ aq ∈ (Set.univ : Set ℝ) ∧ bq ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc aq bq ∧ i ∈ (Set.univ : Set ℕ) ∧ i < n -> x + (i : ℝ) / n ∈ Set.Icc aq (bq + 1) ∧ x + (i : ℝ) / n + θ i / (n : ℝ) ∈ Set.Icc aq (bq + 1)
def lpUniformErrorEstimate (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ) (n : ℕ) (ε : ℝ) (θ : ℕ -> ℝ) : Prop :=
  ∀ (x a b : ℝ), x ∈ (Set.univ : Set ℝ) ∧ a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc a b ->
    |F x - G (n, x)| ≤ ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * |f (x + (i : ℝ) / n + θ i / (n : ℝ)) - f (x + (i : ℝ) / n)| ∧
    (∑ i ∈ Finset.range n, (1 / (n : ℝ)) * |f (x + (i : ℝ) / n + θ i / (n : ℝ)) - f (x + (i : ℝ) / n)|) < ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * ε ∧
    (∑ i ∈ Finset.range n, (1 / (n : ℝ)) * ε) = ε

-- exercise: exercise_2766

theorem proof_gap_exercise_2766_1 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (hf : lpContinuousOn f Set.univ)
  (hG : ∀ n x i, 0 < n ∧ i < n -> G (n, x) = ∑ i ∈ Finset.range n, (1 / (n : ℝ)) * f (x + (i : ℝ) / n))
  (hF : F = lpIntegralLimit f) : lpPointwiseLimit F G := by
  sorry

theorem proof_gap_exercise_2766_2 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (hf : lpContinuousOn f Set.univ) (hF : F = lpIntegralLimit f) (h1 : lpPointwiseLimit F G)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ 0 < n -> F x = lpIntegralLimit f x := by
  sorry

theorem proof_gap_exercise_2766_3 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (hf : lpContinuousOn f Set.univ) (hF : F = lpIntegralLimit f)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ 0 < n -> F x = lpIntegralLimit f x)
  : lpRiemannSplit f F := by
  sorry

theorem proof_gap_exercise_2766_4 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (hf : lpContinuousOn f Set.univ) (h3 : lpRiemannSplit f F)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ 0 < n -> lpThetaIntegralFormula f n x := by
  sorry

theorem proof_gap_exercise_2766_5 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (hf : lpContinuousOn f Set.univ)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) -> ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ x ∈ (Set.univ : Set ℝ) ∧ 0 < n -> lpThetaIntegralFormula f n x)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpContinuousOn f (Set.Icc a (b + 1)) := by
  sorry

theorem proof_gap_exercise_2766_6 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (hf : lpContinuousOn f Set.univ)
  (h5 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpContinuousOn f (Set.Icc a (b + 1)))
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpUniformContinuousOn f (Set.Icc a (b + 1)) := by
  sorry

theorem proof_gap_exercise_2766_7 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (h6 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpUniformContinuousOn f (Set.Icc a (b + 1)))
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∀ (xp aq bq xpp : ℝ), xp ∈ (Set.univ : Set ℝ) ∧ aq ∈ (Set.univ : Set ℝ) ∧ bq ∈ (Set.univ : Set ℝ) ∧ xpp ∈ (Set.univ : Set ℝ) ∧ xp ∈ Set.Icc aq (bq + 1) ∧ xpp ∈ Set.Icc aq (bq + 1) ∧ |xp - xpp| < δ -> |f xp - f xpp| < ε := by
  sorry

theorem proof_gap_exercise_2766_8 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ (N : ℝ) = Int.floor (1 / δ) + 1 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N -> 1 / (n : ℝ) < δ := by
  sorry

theorem proof_gap_exercise_2766_9 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ (N : ℝ) = Int.floor (1 / δ) + 1 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N -> ∃ θ : ℕ -> ℝ, lpThetaIntervalControl n a b θ := by
  sorry

theorem proof_gap_exercise_2766_10 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ (N : ℝ) = Int.floor (1 / δ) + 1 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N -> ∃ θ : ℕ -> ℝ, lpUniformErrorEstimate f F G n ε θ := by
  sorry

theorem proof_gap_exercise_2766_11 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (h10 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 -> ∃ δ : ℝ, δ ∈ (Set.univ : Set ℝ) ∧ δ > 0 ∧ ∃ N : ℕ, N ∈ (Set.univ : Set ℕ) ∧ (N : ℝ) = Int.floor (1 / δ) + 1 ∧ ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n > N -> ∃ θ : ℕ -> ℝ, lpUniformErrorEstimate f F G n ε θ)
  : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpUniformConvergentOn G (Set.Icc a b) F := by
  sorry

theorem proof_gap_exercise_2766_12 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (h11 : ∀ a : ℝ, a ∈ (Set.univ : Set ℝ) -> ∀ b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpUniformConvergentOn G (Set.Icc a b) F)
  : ∀ a b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpUniformConvergentOn G (Set.Icc a b) F := by
  sorry

theorem proof_gap_exercise_2766_13 (f F : ℝ -> ℝ) (G : ℕ × ℝ -> ℝ)
  (h12 : ∀ a b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpUniformConvergentOn G (Set.Icc a b) F)
  : ∀ a b : ℝ, a ∈ (Set.univ : Set ℝ) ∧ b ∈ (Set.univ : Set ℝ) ∧ a < b -> lpUniformConvergentOn G (Set.Icc a b) F := by
  sorry
