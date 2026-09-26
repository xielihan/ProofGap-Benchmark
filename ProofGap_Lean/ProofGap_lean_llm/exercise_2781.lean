import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

def lpAntitoneOnPositive (u : ℕ -> ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m -> m ≤ n -> u n ≤ u m

-- exercise: exercise_2781

theorem proof_gap_exercise_2781_1
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  : ∀ (x : ℝ) (m : ℤ), x = (2 * (m : ℝ)) * Real.pi -> 0 ≤ m ->
      ∀ n : ℕ, 0 < n ->
        Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x)) = 0 := by
  sorry

theorem proof_gap_exercise_2781_2
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  (h1 : ∀ (x : ℝ) (m : ℤ), x = (2 * (m : ℝ)) * Real.pi -> 0 ≤ m ->
      ∀ n : ℕ, 0 < n ->
        Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x)) = 0)
  : ∀ (x : ℝ) (m : ℤ), x ≠ (2 * (m : ℝ)) * Real.pi -> 0 ≤ m ->
        ∀ n : ℕ, 0 < n ->
          |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x))| =
              |Real.sin x| * |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin ((k : ℝ) * x))| ∧
          |Real.sin x| * |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin ((k : ℝ) * x))| ≤
              |Real.sin x| * (1 / |Real.sin (x / 2)|) ∧
        |Real.sin x| * (1 / |Real.sin (x / 2)|) = 2 * |Real.cos (x / 2)| ∧
        2 * |Real.cos (x / 2)| ≤ 2 := by
  sorry

theorem proof_gap_exercise_2781_3
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  (h1 : ∀ (x : ℝ) (m : ℤ), x = (2 * (m : ℝ)) * Real.pi -> 0 ≤ m ->
      ∀ n : ℕ, 0 < n ->
        Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x)) = 0)
  (h2 : ∀ (x : ℝ) (m : ℤ), x ≠ (2 * (m : ℝ)) * Real.pi -> 0 ≤ m ->
      ∀ n : ℕ, 0 < n ->
        |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x))| =
            |Real.sin x| * |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin ((k : ℝ) * x))| ∧
        |Real.sin x| * |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin ((k : ℝ) * x))| ≤
            |Real.sin x| * (1 / |Real.sin (x / 2)|) ∧
        |Real.sin x| * (1 / |Real.sin (x / 2)|) = 2 * |Real.cos (x / 2)| ∧
        2 * |Real.cos (x / 2)| ≤ 2)
  : ∀ (x : ℝ) (n : ℕ), 0 ≤ x -> 0 < n ->
      |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x))| ≤ 2 := by
  sorry

theorem proof_gap_exercise_2781_4
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  (h3 : ∀ (x : ℝ) (n : ℕ), 0 ≤ x -> 0 < n ->
      |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x))| ≤ 2)
  : ∀ x : ℝ, 0 ≤ x ->
      lpAntitoneOnPositive (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹)) := by
  sorry

theorem proof_gap_exercise_2781_5
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  (h4 : ∀ x : ℝ, 0 ≤ x ->
      lpAntitoneOnPositive (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹)))
  : ∀ x : ℝ, 0 ≤ x -> ∀ n : ℕ, 0 < n ->
      1 / Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹) ≤
        1 / Real.rpow (n : ℝ) ((2 : ℝ)⁻¹) := by
  sorry

theorem proof_gap_exercise_2781_6
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  (h5 : ∀ x : ℝ, 0 ≤ x -> ∀ n : ℕ, 0 < n ->
      1 / Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹) ≤
        1 / Real.rpow (n : ℝ) ((2 : ℝ)⁻¹))
  : ∀ x : ℝ, 0 ≤ x ->
      Tendsto (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹)) atTop (𝓝 0) := by
  sorry

theorem proof_gap_exercise_2781_7
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  (ha : ∀ (n : ℕ) (x : ℝ), 0 < n -> 0 ≤ x ->
      a (n, x) = (Real.sin x * Real.sin ((n : ℝ) * x)) /
        Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹))
  (hs : ∀ (n : ℕ) (x : ℝ), 0 < n -> 0 ≤ x ->
      s (n, x) = Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => a (k, x)))
  (h3 : ∀ (x : ℝ) (n : ℕ), 0 ≤ x -> 0 < n ->
      |Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => Real.sin x * Real.sin ((k : ℝ) * x))| ≤ 2)
  (h4 : ∀ x : ℝ, 0 ≤ x ->
      lpAntitoneOnPositive (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹)))
  (h6 : ∀ x : ℝ, 0 ≤ x ->
      Tendsto (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹)) atTop (𝓝 0))
  : TendstoUniformlyOn (fun n x => s (n, x)) (fun _ => S) atTop {x : ℝ | 0 ≤ x} := by
  sorry

theorem proof_gap_exercise_2781_8
  (a : ℕ × ℝ -> ℝ) (s : ℕ × ℝ -> ℝ) (S : ℝ)
  (h7 : TendstoUniformlyOn (fun n x => s (n, x)) (fun _ => S) atTop {x : ℝ | 0 ≤ x})
  : ∀ (a₁ : ℕ × ℝ -> ℝ) (s₁ : ℕ × ℝ -> ℝ) (S₁ : ℝ),
      (∀ (n : ℕ) (x : ℝ), 0 < n -> 0 ≤ x ->
        a₁ (n, x) = (Real.sin x * Real.sin ((n : ℝ) * x)) /
          Real.rpow ((n : ℝ) + x) ((2 : ℝ)⁻¹)) ->
        (∀ (n : ℕ) (x : ℝ), 0 < n -> 0 ≤ x ->
          s₁ (n, x) = Finset.sum (Finset.Icc (1 : ℕ) n) (fun k => a₁ (k, x))) ->
      TendstoUniformlyOn (fun n x => s₁ (n, x)) (fun _ => S₁) atTop {x : ℝ | 0 ≤ x} := by
  sorry
