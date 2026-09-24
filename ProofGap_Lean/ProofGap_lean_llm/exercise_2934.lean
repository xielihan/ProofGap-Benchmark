import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def DefInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x in a..b, f x
noncomputable def sqrtn (_n : ℕ) (x : ℝ) : ℝ := Real.sqrt x
noncomputable def diff {α : Type*} (_x : α) : ℝ := 0
def approx (eps x y : ℝ) : Prop := |x - y| ≤ eps

noncomputable def ex2934_speedByDeriv (x y : ℝ → ℝ) : ℝ → ℝ :=
  fun t => sqrtn 2 (deriv x t ^ 2 + deriv y t ^ 2)
noncomputable def ex2934_speedByTrig (a b : ℝ) : ℝ → ℝ :=
  fun t => sqrtn 2 (a ^ 2 * Real.cos t ^ 2 + b ^ 2 * Real.sin t ^ 2)
noncomputable def ex2934_speedByEcc (a ε : ℝ) : ℝ → ℝ :=
  fun t => a * sqrtn 2 (1 - ε ^ 2 * Real.sin t ^ 2)
noncomputable def ex2934_binomIntegrand (ε : ℝ) : ℝ → ℝ :=
  fun t => 1 - (1 /. 2) * ε ^ 2 * Real.sin t ^ 2 -
    (1 /. ((Nat.factorial 2 : ℝ) * 2 ^ 2)) * ε ^ 4 * Real.sin t ^ 4 -
    ((1 * 3 : ℝ) /. ((Nat.factorial 3 : ℝ) * 2 ^ 3)) * ε ^ 6 * Real.sin t ^ 6
noncomputable def ex2934_substitutedValue : ℝ :=
  2 * Real.pi * (1 - (1 /. 4) * (3 /. 4) - (3 /. 64) * (9 /. 16) -
    (5 /. 256) * (27 /. 64) - ((5 * 27 * 3 : ℝ) /. (256 * 64 * 4)))

-- exercise: exercise_2934

theorem proof_gap_exercise_2934_1
    (a b : ℝ) (x y : ℝ → ℝ) (s ε : ℝ)
    (h1 : a ∈ (Set.univ : Set ℝ)) (h2 : b ∈ (Set.univ : Set ℝ))
    (h3 : s ∈ (Set.univ : Set ℝ)) (h4 : ε ∈ (Set.univ : Set ℝ))
    (h5 : a = 1) (h6 : b = 1 /. 2)
    (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.sin t)
    (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.cos t)
    (h9 : ε = sqrtn 2 (a ^ 2 - b ^ 2) /. a) :
    diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByDeriv x y) := by
  sorry

theorem proof_gap_exercise_2934_2
    (a b : ℝ) (x y : ℝ → ℝ) (s ε : ℝ)
    (h1 : a ∈ (Set.univ : Set ℝ)) (h2 : b ∈ (Set.univ : Set ℝ))
    (h3 : s ∈ (Set.univ : Set ℝ)) (h4 : ε ∈ (Set.univ : Set ℝ))
    (h5 : a = 1) (h6 : b = 1 /. 2)
    (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.sin t)
    (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.cos t)
    (h9 : ε = sqrtn 2 (a ^ 2 - b ^ 2) /. a)
    (h10 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByDeriv x y)) :
    diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByTrig a b) := by
  sorry

theorem proof_gap_exercise_2934_3
    (a b : ℝ) (x y : ℝ → ℝ) (s ε : ℝ)
    (h1 : a ∈ (Set.univ : Set ℝ)) (h2 : b ∈ (Set.univ : Set ℝ))
    (h3 : s ∈ (Set.univ : Set ℝ)) (h4 : ε ∈ (Set.univ : Set ℝ))
    (h5 : a = 1) (h6 : b = 1 /. 2)
    (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.sin t)
    (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.cos t)
    (h9 : ε = sqrtn 2 (a ^ 2 - b ^ 2) /. a)
    (h10 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByDeriv x y))
    (h11 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByTrig a b)) :
    diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByEcc a ε) := by
  sorry

theorem proof_gap_exercise_2934_4
    (a b : ℝ) (x y : ℝ → ℝ) (s ε : ℝ)
    (h1 : a ∈ (Set.univ : Set ℝ)) (h2 : b ∈ (Set.univ : Set ℝ))
    (h3 : s ∈ (Set.univ : Set ℝ)) (h4 : ε ∈ (Set.univ : Set ℝ))
    (h5 : a = 1) (h6 : b = 1 /. 2)
    (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.sin t)
    (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.cos t)
    (h9 : ε = sqrtn 2 (a ^ 2 - b ^ 2) /. a)
    (h10 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByDeriv x y))
    (h11 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByTrig a b))
    (h12 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByEcc a ε)) :
    s = 4 * a * DefInt 0 (Real.pi /. 2) (fun t => sqrtn 2 (1 - ε ^ 2 * Real.sin t ^ 2)) := by
  sorry

theorem proof_gap_exercise_2934_5
    (a b : ℝ) (x y : ℝ → ℝ) (s ε : ℝ)
    (h1 : a ∈ (Set.univ : Set ℝ)) (h2 : b ∈ (Set.univ : Set ℝ))
    (h3 : s ∈ (Set.univ : Set ℝ)) (h4 : ε ∈ (Set.univ : Set ℝ))
    (h5 : a = 1) (h6 : b = 1 /. 2)
    (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.sin t)
    (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.cos t)
    (h9 : ε = sqrtn 2 (a ^ 2 - b ^ 2) /. a)
    (h10 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByDeriv x y))
    (h11 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByTrig a b))
    (h12 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByEcc a ε))
    (h13 : s = 4 * a * DefInt 0 (Real.pi /. 2) (fun t => sqrtn 2 (1 - ε ^ 2 * Real.sin t ^ 2))) :
    s = 4 * a * DefInt 0 (Real.pi /. 2) (ex2934_binomIntegrand ε) := by
  sorry

theorem proof_gap_exercise_2934_6
    (a b : ℝ) (x y : ℝ → ℝ) (s ε : ℝ)
    (h1 : a ∈ (Set.univ : Set ℝ)) (h2 : b ∈ (Set.univ : Set ℝ))
    (h3 : s ∈ (Set.univ : Set ℝ)) (h4 : ε ∈ (Set.univ : Set ℝ))
    (h5 : a = 1) (h6 : b = 1 /. 2)
    (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.sin t)
    (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.cos t)
    (h9 : ε = sqrtn 2 (a ^ 2 - b ^ 2) /. a)
    (h10 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByDeriv x y))
    (h11 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByTrig a b))
    (h12 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByEcc a ε))
    (h13 : s = 4 * a * DefInt 0 (Real.pi /. 2) (fun t => sqrtn 2 (1 - ε ^ 2 * Real.sin t ^ 2)))
    (h14 : s = 4 * a * DefInt 0 (Real.pi /. 2) (ex2934_binomIntegrand ε)) :
    approx (1 /. 100) s ex2934_substitutedValue := by
  sorry

theorem proof_gap_exercise_2934_7
    (a b : ℝ) (x y : ℝ → ℝ) (s ε : ℝ)
    (h1 : a ∈ (Set.univ : Set ℝ)) (h2 : b ∈ (Set.univ : Set ℝ))
    (h3 : s ∈ (Set.univ : Set ℝ)) (h4 : ε ∈ (Set.univ : Set ℝ))
    (h5 : a = 1) (h6 : b = 1 /. 2)
    (h7 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → x t = a * Real.sin t)
    (h8 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ 0 ≤ t ∧ t ≤ 2 * Real.pi → y t = b * Real.cos t)
    (h9 : ε = sqrtn 2 (a ^ 2 - b ^ 2) /. a)
    (h10 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByDeriv x y))
    (h11 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByTrig a b))
    (h12 : diff s = diff (fun t : ℝ => t) * 0 + diff (ex2934_speedByEcc a ε))
    (h13 : s = 4 * a * DefInt 0 (Real.pi /. 2) (fun t => sqrtn 2 (1 - ε ^ 2 * Real.sin t ^ 2)))
    (h14 : s = 4 * a * DefInt 0 (Real.pi /. 2) (ex2934_binomIntegrand ε))
    (h15 : approx (1 /. 100) s ex2934_substitutedValue) :
    |s - 4.84| ≤ 1 /. 100 := by
  sorry
