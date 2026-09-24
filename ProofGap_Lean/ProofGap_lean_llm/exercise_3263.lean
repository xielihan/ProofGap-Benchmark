import Mathlib

set_option linter.style.longLine false

open scoped BigOperators

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

noncomputable def lpPartialDeriv₂ (coord : Nat) (f : ℝ × ℝ -> ℝ) : ℝ × ℝ -> ℝ :=
  fun p => fderiv ℝ f p (if coord = 1 then (1, 0) else (0, 1))

noncomputable def lpFunDeri₂ (f : ℝ × ℝ -> ℝ) (coord order : Nat) : ℝ × ℝ -> ℝ :=
  Nat.iterate (lpPartialDeriv₂ coord) order f

noncomputable def lpFunDeri₁ (f : ℝ -> ℝ) (order : Nat) : ℝ -> ℝ :=
  Nat.iterate deriv order f

noncomputable def lpRisingProduct (m n : Nat) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, ((m + i : Nat) : ℝ)

-- exercise: exercise_3263
-- Exercise 3263, gap 1
theorem proof_gap_exercise_3263_1
  (u : ℝ × ℝ -> ℝ)
  (m n : Nat)
  (hm_nonneg : m ∈ (Set.univ : Set Nat))
  (hm_pos : m ∈ {k : Nat | 0 < k})
  (hn_nonneg : n ∈ (Set.univ : Set Nat))
  (hn_pos : n ∈ {k : Nat | 0 < k})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = (x + y) /. (x - y))
  : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = 1 + (2 * y) /. (x - y) := by
  sorry

-- Exercise 3263, gap 2
theorem proof_gap_exercise_3263_2
  (u : ℝ × ℝ -> ℝ)
  (m n : Nat)
  (hm_nonneg : m ∈ (Set.univ : Set Nat))
  (hm_pos : m ∈ {k : Nat | 0 < k})
  (hn_nonneg : n ∈ (Set.univ : Set Nat))
  (hn_pos : n ∈ {k : Nat | 0 < k})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = (x + y) /. (x - y))
  (hu_split : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = 1 + (2 * y) /. (x - y))
  : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ u 1 m (x, y) = (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * ((2 * y) /. ((x - y) ^ (m + 1))) := by
  sorry

-- Exercise 3263, gap 3
theorem proof_gap_exercise_3263_3
  (u : ℝ × ℝ -> ℝ)
  (m n : Nat)
  (hm_nonneg : m ∈ (Set.univ : Set Nat))
  (hm_pos : m ∈ {k : Nat | 0 < k})
  (hn_nonneg : n ∈ (Set.univ : Set Nat))
  (hn_pos : n ∈ {k : Nat | 0 < k})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = (x + y) /. (x - y))
  (hu_split : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = 1 + (2 * y) /. (x - y))
  (hm_deriv : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ u 1 m (x, y) = (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * ((2 * y) /. ((x - y) ^ (m + 1))))
  : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ (lpFunDeri₂ u 1 m) 2 n (x, y) =
      2 * (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (y * lpFunDeri₁ (fun yy : ℝ => 1 /. ((x - yy) ^ (m + 1))) n y
        + ((Nat.choose n 1 : Nat) : ℝ) * deriv (fun yy : ℝ => yy) y *
          lpFunDeri₁ (fun yy : ℝ => 1 /. ((x - yy) ^ (m + 1))) (n - 1) y) := by
  sorry

-- Exercise 3263, gap 4
theorem proof_gap_exercise_3263_4
  (u : ℝ × ℝ -> ℝ)
  (m n : Nat)
  (hm_nonneg : m ∈ (Set.univ : Set Nat))
  (hm_pos : m ∈ {k : Nat | 0 < k})
  (hn_nonneg : n ∈ (Set.univ : Set Nat))
  (hn_pos : n ∈ {k : Nat | 0 < k})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = (x + y) /. (x - y))
  (hu_split : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = 1 + (2 * y) /. (x - y))
  (hm_deriv : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ u 1 m (x, y) = (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * ((2 * y) /. ((x - y) ^ (m + 1))))
  (hleibniz : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ (lpFunDeri₂ u 1 m) 2 n (x, y) =
      2 * (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (y * lpFunDeri₁ (fun yy : ℝ => 1 /. ((x - yy) ^ (m + 1))) n y
        + ((Nat.choose n 1 : Nat) : ℝ) * deriv (fun yy : ℝ => yy) y *
          lpFunDeri₁ (fun yy : ℝ => 1 /. ((x - yy) ^ (m + 1))) (n - 1) y))
  : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ (lpFunDeri₂ u 1 m) 2 n (x, y) =
      2 * (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (((lpRisingProduct m n) * y) /. ((x - y) ^ (m + n + 1))
        + (((n : ℝ) * lpRisingProduct m (n - 1)) /. ((x - y) ^ (m + n)))) := by
  sorry

-- Exercise 3263, gap 5
theorem proof_gap_exercise_3263_5
  (u : ℝ × ℝ -> ℝ)
  (m n : Nat)
  (hm_nonneg : m ∈ (Set.univ : Set Nat))
  (hm_pos : m ∈ {k : Nat | 0 < k})
  (hn_nonneg : n ∈ (Set.univ : Set Nat))
  (hn_pos : n ∈ {k : Nat | 0 < k})
  (hu : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = (x + y) /. (x - y))
  (hu_split : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    u (x, y) = 1 + (2 * y) /. (x - y))
  (hm_deriv : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ u 1 m (x, y) = (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * ((2 * y) /. ((x - y) ^ (m + 1))))
  (hleibniz : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ (lpFunDeri₂ u 1 m) 2 n (x, y) =
      2 * (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (y * lpFunDeri₁ (fun yy : ℝ => 1 /. ((x - yy) ^ (m + 1))) n y
        + ((Nat.choose n 1 : Nat) : ℝ) * deriv (fun yy : ℝ => yy) y *
          lpFunDeri₁ (fun yy : ℝ => 1 /. ((x - yy) ^ (m + 1))) (n - 1) y))
  (hexpanded : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ (lpFunDeri₂ u 1 m) 2 n (x, y) =
      2 * (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (((lpRisingProduct m n) * y) /. ((x - y) ^ (m + n + 1))
        + (((n : ℝ) * lpRisingProduct m (n - 1)) /. ((x - y) ^ (m + n)))))
  : ∀ x y : ℝ, x ∈ (Set.univ : Set ℝ) ∧ y ∈ (Set.univ : Set ℝ) ∧ x ≠ y ->
    lpFunDeri₂ (lpFunDeri₂ u 1 m) 2 n (x, y) =
      (2 * (-1 : ℝ) ^ m * (Nat.factorial (m + n - 1) : ℝ) * ((n : ℝ) * x + (m : ℝ) * y))
        /. ((x - y) ^ (m + n + 1)) := by
  sorry
