import Mathlib

set_option linter.style.longLine false
open scoped Topology
open Filter

-- Derivative values are expressed with HasDerivAt, including existence.
-- Gap 8 is equality of partial-function graphs: there is no integer branch.
-- Equality/inequality of limits includes existence of the finite real limits.

/- Exercise 1001, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)

GOAL:
forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)

METHOD:
-/
theorem proof_gap_exercise_1001_1
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x := by
  sorry

/- Exercise 1001, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)
3. forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)

GOAL:
forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx))

METHOD:
-/
theorem proof_gap_exercise_1001_2
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x)
  : ∀ k : ℤ, ∃ L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  sorry

/- Exercise 1001, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)
3. forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)
4. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx))

GOAL:
forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx)) = k * π * (-1)^{k}

METHOD:
-/
theorem proof_gap_exercise_1001_3
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x)
  (h3 : ∀ k : ℤ, ∃ L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L))
  : ∀ k : ℤ, Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)) := by
  sorry

/- Exercise 1001, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)
3. forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)
4. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx))
5. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx)) = k * π * (-1)^{k}

GOAL:
forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = k * π * (-1)^{k}

METHOD:
-/
theorem proof_gap_exercise_1001_4
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x)
  (h3 : ∀ k : ℤ, ∃ L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L))
  (h4 : ∀ k : ℤ, Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)) := by
  sorry

/- Exercise 1001, gap 5
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)
3. forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)
4. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx))
5. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx)) = k * π * (-1)^{k}
6. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = k * π * (-1)^{k}

GOAL:
forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^- } (frac(f(k + Δx) - f(k), Δx)) = π * (k - 1) * (-1)^{k}

METHOD:
-/
theorem proof_gap_exercise_1001_5
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x)
  (h3 : ∀ k : ℤ, ∃ L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L))
  (h4 : ∀ k : ℤ, Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  (h5 : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[<] (0 : ℝ)) (𝓝 (Real.pi * ((k : ℝ) - 1) * (-1 : ℝ) ^ k)) := by
  sorry

/- Exercise 1001, gap 6
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)
3. forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)
4. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx))
5. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx)) = k * π * (-1)^{k}
6. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = k * π * (-1)^{k}
7. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^- } (frac(f(k + Δx) - f(k), Δx)) = π * (k - 1) * (-1)^{k}

GOAL:
forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) ≠ lim_{ Δx → 0^- } (frac(f(k + Δx) - f(k), Δx))

METHOD:
-/
theorem proof_gap_exercise_1001_6
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x)
  (h3 : ∀ k : ℤ, ∃ L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L))
  (h4 : ∀ k : ℤ, Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  (h5 : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  (h6 : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[<] (0 : ℝ)) (𝓝 (Real.pi * ((k : ℝ) - 1) * (-1 : ℝ) ^ k)))
  : ∀ k : ℤ, ∃ R L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 R) ∧ Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[<] (0 : ℝ)) (𝓝 L) ∧ R ≠ L := by
  sorry

/- Exercise 1001, gap 7
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)
3. forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)
4. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx))
5. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx)) = k * π * (-1)^{k}
6. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = k * π * (-1)^{k}
7. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^- } (frac(f(k + Δx) - f(k), Δx)) = π * (k - 1) * (-1)^{k}
8. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) ≠ lim_{ Δx → 0^- } (frac(f(k + Δx) - f(k), Δx))

GOAL:
forall (k), k ∈ IntegerSet ⇒ ¬DiffableFuncAt(f, k)

METHOD:
-/
theorem proof_gap_exercise_1001_7
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x)
  (h3 : ∀ k : ℤ, ∃ L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L))
  (h4 : ∀ k : ℤ, Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  (h5 : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  (h6 : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[<] (0 : ℝ)) (𝓝 (Real.pi * ((k : ℝ) - 1) * (-1 : ℝ) ^ k)))
  (h7 : ∀ k : ℤ, ∃ R L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 R) ∧ Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[<] (0 : ℝ)) (𝓝 L) ∧ R ≠ L)
  : ∀ k : ℤ, ¬ DifferentiableAt ℝ f (k : ℝ) := by
  sorry

/- Exercise 1001, gap 8
PROOF GAP @8
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = floor(x) * sin(π * x)
3. forall (x), x ∈ RealSet ∧ x ∉ IntegerSet ⇒ FunDeri(f, 1, 1)(x) = π * floor(x) * cos(π * x)
4. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx))
5. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(k * cos(k * π) * sin(π * Δx), Δx)) = k * π * (-1)^{k}
6. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) = k * π * (-1)^{k}
7. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^- } (frac(f(k + Δx) - f(k), Δx)) = π * (k - 1) * (-1)^{k}
8. forall (k), k ∈ IntegerSet ⇒ lim_{ Δx → 0^+ } (frac(f(k + Δx) - f(k), Δx)) ≠ lim_{ Δx → 0^- } (frac(f(k + Δx) - f(k), Δx))
9. forall (k), k ∈ IntegerSet ⇒ ¬DiffableFuncAt(f, k)

GOAL:
FunDeri(f, 1, 1) = (fun x [x ∈ RealSet] . cases{ π * floor(x) * cos(π * x) if x ∉ IntegerSet })

METHOD:
-/
theorem proof_gap_exercise_1001_8
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = (⌊x⌋ : ℝ) * Real.sin (Real.pi * x))
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∉ Set.range (fun k : ℤ => (k : ℝ)) → HasDerivAt f (Real.pi * (⌊x⌋ : ℝ) * Real.cos (Real.pi * x)) x)
  (h3 : ∀ k : ℤ, ∃ L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧ Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 L))
  (h4 : ∀ k : ℤ, Tendsto (fun dx : ℝ => ((k : ℝ) * Real.cos ((k : ℝ) * Real.pi) * Real.sin (Real.pi * dx)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  (h5 : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 ((k : ℝ) * Real.pi * (-1 : ℝ) ^ k)))
  (h6 : ∀ k : ℤ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[<] (0 : ℝ)) (𝓝 (Real.pi * ((k : ℝ) - 1) * (-1 : ℝ) ^ k)))
  (h7 : ∀ k : ℤ, ∃ R L : ℝ, Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[>] (0 : ℝ)) (𝓝 R) ∧ Tendsto (fun dx : ℝ => (f ((k : ℝ) + dx) - f (k : ℝ)) / dx) (𝓝[<] (0 : ℝ)) (𝓝 L) ∧ R ≠ L)
  (h8 : ∀ k : ℤ, ¬ DifferentiableAt ℝ f (k : ℝ))
  : {p : ℝ × ℝ | HasDerivAt f p.2 p.1} = {p : ℝ × ℝ | p.1 ∉ Set.range (fun k : ℤ => (k : ℝ)) ∧ p.2 = Real.pi * (⌊p.1⌋ : ℝ) * Real.cos (Real.pi * p.1)} := by
  sorry

