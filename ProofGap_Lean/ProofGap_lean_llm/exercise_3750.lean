import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false

open scoped Topology
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def ex3750_integrand (n x : ℝ) : ℝ :=
  Real.sin (x + x ^ (2 : ℕ)) /. x ^ n

def convergentImproper (I : ℝ) : Prop :=
  ∃ approximants : ℕ -> ℝ, Tendsto approximants atTop (𝓝 I)

def divergentImproper (I : ℝ) : Prop :=
  ∀ L : ℝ, ¬ ∃ approximants : ℕ -> ℝ, Tendsto approximants atTop (𝓝 L)

noncomputable def ex3750_xi (k : ℕ) : ℝ :=
  (Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + Real.pi) - 1) /. 2

noncomputable def ex3750_eta (k : ℕ) : ℝ :=
  (Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + 2 * Real.pi) - 1) /. 2

-- exercise: exercise_3750

theorem proof_gap_exercise_3750_1 (n : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), ex3750_integrand n x)
      = (∫ x in (0 : ℝ)..1, ex3750_integrand n x)
        + (∫ x in Set.Ioi (1 : ℝ), ex3750_integrand n x) := by sorry

theorem proof_gap_exercise_3750_2 (n : ℝ) :
    convergentImproper (∫ x in (0 : ℝ)..1, ex3750_integrand n x) ↔ n < 2 := by sorry

theorem proof_gap_exercise_3750_3 (n : ℝ) :
    ∀ k : ℕ, ∀ a : ℕ -> ℝ,
      a 0 = 1 ->
      (∀ k : ℕ, 0 < a k ∧ a k < a (k + 1)) ->
      Tendsto a atTop atTop -> n > -1 ->
      (∫ x in a k..a (k + 1), ex3750_integrand n x)
        = -(∫ x in a k..a (k + 1),
          deriv (fun u : ℝ => Real.cos (u + u ^ (2 : ℕ))) x /. (x ^ n * (1 + 2 * x))) := by sorry

theorem proof_gap_exercise_3750_4 (n : ℝ) :
    ∀ k : ℕ, ∀ a : ℕ -> ℝ,
      a 0 = 1 ->
      (∀ k : ℕ, 0 < a k ∧ a k < a (k + 1)) ->
      Tendsto a atTop atTop -> n > -1 ->
      (∫ x in a k..a (k + 1), ex3750_integrand n x)
        = -((Real.cos (a (k + 1) + (a (k + 1)) ^ (2 : ℕ)) /. ((a (k + 1)) ^ n * (1 + 2 * a (k + 1))))
            - (Real.cos (a k + (a k) ^ (2 : ℕ)) /. ((a k) ^ n * (1 + 2 * a k))))
          - (∫ x in a k..a (k + 1),
            ((2 * (n + 1) * x + n) * Real.cos (x + x ^ (2 : ℕ))) /. (x ^ (n + 1) * (1 + 2 * x) ^ (2 : ℕ))) := by sorry

theorem proof_gap_exercise_3750_5 (n : ℝ) :
    ∀ m p : ℕ, 0 < p ->
      ∀ a : ℕ -> ℝ,
        a 0 = 1 ->
        (∀ k : ℕ, 0 < a k ∧ a k < a (k + 1)) ->
        Tendsto a atTop atTop -> n > -1 ->
        abs ((Finset.range p).sum
          (fun k => ∫ x in a (m + k)..a (m + k + 1), ex3750_integrand n x))
          ≤ 1 /. (2 * (a m) ^ (n + 1))
            + 1 /. (2 * (a (m + p)) ^ (n + 1))
            + (∫ x in a m..a (m + p),
              (2 * (n + 1) * x + |n|) /. (x ^ (n + 1) * (1 + 2 * x) ^ (2 : ℕ))) := by sorry

theorem proof_gap_exercise_3750_6 (n : ℝ) :
    n > -1 ->
      Tendsto (fun x : ℝ =>
        x ^ (n + 2) * ((2 * (n + 1) * x + |n|) /. (x ^ (n + 1) * (1 + 2 * x) ^ (2 : ℕ))))
        atTop (𝓝 ((n + 1) /. 2)) := by sorry

theorem proof_gap_exercise_3750_7 (n : ℝ) :
    n > -1 -> n + 2 > 1 := by sorry

theorem proof_gap_exercise_3750_8 (n : ℝ) :
    n > -1 ->
      convergentImproper (∫ x in Set.Ioi (1 : ℝ),
        (2 * (n + 1) * x + |n|) /. (x ^ (n + 1) * (1 + 2 * x) ^ (2 : ℕ))) := by sorry

theorem proof_gap_exercise_3750_9 (n : ℝ) :
    n > -1 ->
      ∀ a : ℕ -> ℝ,
        a 0 = 1 ->
        (∀ k : ℕ, 0 < a k ∧ a k < a (k + 1)) ->
        Tendsto a atTop atTop ->
        ∀ ε : ℝ, ε > 0 ->
          ∃ N : ℕ, ∀ m p : ℕ, N < m -> 0 < p ->
            abs ((Finset.range p).sum
              (fun k => ∫ x in a (m + k)..a (m + k + 1), ex3750_integrand n x)) < ε := by sorry

theorem proof_gap_exercise_3750_10 (n : ℝ) :
    n > -1 ->
      ∀ a : ℕ -> ℝ,
        a 0 = 1 ->
        (∀ k : ℕ, 0 < a k ∧ a k < a (k + 1)) ->
        Tendsto a atTop atTop ->
        convergentImproper (∑' k : ℕ, ∫ x in a k..a (k + 1), ex3750_integrand n x) := by sorry

theorem proof_gap_exercise_3750_11 (n : ℝ) :
    n > -1 -> convergentImproper (∫ x in Set.Ioi (1 : ℝ), ex3750_integrand n x) := by sorry

theorem proof_gap_exercise_3750_12 (n : ℝ) :
    n ≤ -1 ->
      ∀ k : ℕ, 0 < k ->
        ex3750_xi k ^ (2 : ℕ) + ex3750_xi k = 2 * (k : ℝ) * Real.pi + (Real.pi /. 4) ∧
        ex3750_eta k ^ (2 : ℕ) + ex3750_eta k = 2 * (k : ℝ) * Real.pi + (Real.pi /. 2) := by sorry

theorem proof_gap_exercise_3750_13 (n : ℝ) :
    n ≤ -1 -> ∀ k : ℕ, 0 < k -> ex3750_eta k > ex3750_xi k := by sorry

theorem proof_gap_exercise_3750_14 (n : ℝ) :
    n ≤ -1 -> Tendsto ex3750_xi atTop atTop := by sorry

theorem proof_gap_exercise_3750_15 (n : ℝ) :
    ∀ k : ℕ, 0 < k -> n ≤ -1 ->
      (∫ x in ex3750_xi k..ex3750_eta k, ex3750_integrand n x)
        > (1 /. Real.sqrt 2) * (∫ x in ex3750_xi k..ex3750_eta k, x ^ (-n)) := by sorry

theorem proof_gap_exercise_3750_16 (n : ℝ) :
    ∀ k : ℕ, 0 < k -> n ≤ -1 ->
      (1 /. Real.sqrt 2) * (∫ x in ex3750_xi k..ex3750_eta k, x ^ (-n))
        ≥ (1 /. Real.sqrt 2) * (∫ x in ex3750_xi k..ex3750_eta k, x) := by sorry

theorem proof_gap_exercise_3750_17 (n : ℝ) :
    ∀ k : ℕ, 0 < k -> n ≤ -1 ->
      (1 /. Real.sqrt 2) * (∫ x in ex3750_xi k..ex3750_eta k, x)
        > (1 /. Real.sqrt 2) * ex3750_xi k * (ex3750_eta k - ex3750_xi k) := by sorry

theorem proof_gap_exercise_3750_18 (n : ℝ) :
    ∀ k : ℕ, 0 < k -> n ≤ -1 ->
      (∫ x in ex3750_xi k..ex3750_eta k, ex3750_integrand n x)
        > (1 /. Real.sqrt 2) * ex3750_xi k * (ex3750_eta k - ex3750_xi k) := by sorry

theorem proof_gap_exercise_3750_19 (n : ℝ) :
    ∀ k : ℕ, 0 < k -> n ≤ -1 ->
      (1 /. Real.sqrt 2) * ex3750_xi k * (ex3750_eta k - ex3750_xi k)
        = (Real.pi /. (4 * Real.sqrt 2)) *
            ((Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + Real.pi) - 1) /.
              (Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + 2 * Real.pi)
                + Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + Real.pi))) := by sorry

theorem proof_gap_exercise_3750_20 (n : ℝ) :
    n ≤ -1 ->
      Tendsto
        (fun k : ℕ =>
          (Real.pi /. (4 * Real.sqrt 2)) *
            ((Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + Real.pi) - 1) /.
              (Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + 2 * Real.pi)
                + Real.sqrt (1 + 8 * (k : ℝ) * Real.pi + Real.pi))))
        atTop (𝓝 (Real.pi /. (8 * Real.sqrt 2))) := by sorry

theorem proof_gap_exercise_3750_21 (n : ℝ) :
    n ≤ -1 -> divergentImproper (∫ x in Set.Ioi (1 : ℝ), ex3750_integrand n x) := by sorry

theorem proof_gap_exercise_3750_22 (n : ℝ) :
    convergentImproper (∫ x in Set.Ioi (0 : ℝ), ex3750_integrand n x) ↔ -1 < n ∧ n < 2 := by sorry
