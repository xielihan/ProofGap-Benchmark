import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def ConditionalConvergentSeries (a : ℕ -> ℝ) : Prop :=
  Summable a ∧ ¬ Summable (fun n => ‖a n‖)

noncomputable def newtonTerm (x p : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n then (1 /. ((n : ℝ) ^ p)) * ((∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) /. (n !)) else 0

noncomputable def auxTerm2739 (t p : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n then ((-1 : ℝ) ^ (n - 1)) * ((∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)) /. ((n !) * ((n : ℝ) ^ p))) else 0

-- exercise: exercise_2739_2

theorem proof_gap_exercise_2739_2_1
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)) := by
  sorry

theorem proof_gap_exercise_2739_2_2
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)))
  : (fun n => newtonTerm x p n) = (fun n => - auxTerm2739 t p n) := by
  sorry

theorem proof_gap_exercise_2739_2_3
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)))
  (h6 : (fun n => newtonTerm x p n) = (fun n => - auxTerm2739 t p n))
  : p > t + 1 → Summable (fun n => ‖newtonTerm x p n‖) := by
  sorry

theorem proof_gap_exercise_2739_2_4
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)))
  (h6 : (fun n => newtonTerm x p n) = (fun n => - auxTerm2739 t p n))
  (h7 : p > t + 1 → Summable (fun n => ‖newtonTerm x p n‖))
  : p > -x → Summable (fun n => ‖newtonTerm x p n‖) := by
  sorry

theorem proof_gap_exercise_2739_2_5
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)))
  (h6 : (fun n => newtonTerm x p n) = (fun n => - auxTerm2739 t p n))
  (h7 : p > t + 1 → Summable (fun n => ‖newtonTerm x p n‖))
  (h8 : p > -x → Summable (fun n => ‖newtonTerm x p n‖))
  : x ∈ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m} → Summable (fun n => ‖newtonTerm x p n‖) := by
  sorry

theorem proof_gap_exercise_2739_2_6
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)))
  (h6 : (fun n => newtonTerm x p n) = (fun n => - auxTerm2739 t p n))
  (h7 : p > t + 1 → Summable (fun n => ‖newtonTerm x p n‖))
  (h8 : p > -x → Summable (fun n => ‖newtonTerm x p n‖))
  (h9 : x ∈ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m} → Summable (fun n => ‖newtonTerm x p n‖))
  : t < p ∧ p ≤ t + 1 → ConditionalConvergentSeries (newtonTerm x p) := by
  sorry

theorem proof_gap_exercise_2739_2_7
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)))
  (h6 : (fun n => newtonTerm x p n) = (fun n => - auxTerm2739 t p n))
  (h7 : p > t + 1 → Summable (fun n => ‖newtonTerm x p n‖))
  (h8 : p > -x → Summable (fun n => ‖newtonTerm x p n‖))
  (h9 : x ∈ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m} → Summable (fun n => ‖newtonTerm x p n‖))
  (h10 : t < p ∧ p ≤ t + 1 → ConditionalConvergentSeries (newtonTerm x p))
  : -(1 + x) < p ∧ p ≤ -x ∧ x ∉ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m} →
      ConditionalConvergentSeries (newtonTerm x p) := by
  sorry

theorem proof_gap_exercise_2739_2_8
  (x p t : ℝ)
  (h4 : t = -(1 + x))
  (h5 : ∀ n : ℕ, n ∈ (Set.univ : Set ℕ) ∧ n ∈ {n : ℕ | 0 < n} →
      (∏ k ∈ Finset.Icc (0 : ℕ) (n - 1), (x - (k : ℝ))) =
        -((-1 : ℝ) ^ (n - 1)) * (∏ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) + t)))
  (h6 : (fun n => newtonTerm x p n) = (fun n => - auxTerm2739 t p n))
  (h7 : p > t + 1 → Summable (fun n => ‖newtonTerm x p n‖))
  (h8 : p > -x → Summable (fun n => ‖newtonTerm x p n‖))
  (h9 : x ∈ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m} → Summable (fun n => ‖newtonTerm x p n‖))
  (h10 : t < p ∧ p ≤ t + 1 → ConditionalConvergentSeries (newtonTerm x p))
  (h11 : -(1 + x) < p ∧ p ≤ -x ∧ x ∉ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m} →
      ConditionalConvergentSeries (newtonTerm x p))
  : ((x, p) ∈ {xp : ℝ × ℝ |
        let x := xp.1
        let p := xp.2
        ((p > -x ∨ x ∈ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m}) ∧ Summable (fun n => ‖newtonTerm x p n‖)) ∨
          (-(1 + x) < p ∧ p ≤ -x ∧ x ∉ {m : ℝ | ∃ n : ℕ, (n : ℝ) = m} ∧ ConditionalConvergentSeries (newtonTerm x p))})
      ↔ (Summable (fun n => ‖newtonTerm x p n‖) ∧ ConditionalConvergentSeries (newtonTerm x p)) := by
  sorry
