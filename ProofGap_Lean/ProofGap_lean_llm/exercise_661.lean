import Mathlib

open scoped BigOperators Topology
open Filter

-- The multiplier is the integer floor, including for negative x.
noncomputable def exercise661Denom (g : ℕ × ℝ → ℝ) (x : ℝ) : ℝ :=
  (⌊x⌋ : ℤ) * ((∑ k ∈ Finset.Icc 1 (Int.toNat ⌊x⌋), |g (k, x)|) + 1)

-- Equality of the restricted functions imposes no condition outside Ioi x₀.

/- Exercise 661, gap 1
PROOF GAP @1
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. forall (n), n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
4. N = floor(x_{0}) + 1
5. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
GOAL:
f : IntervalLoRo(x_{0}, +∞) → RealSet

METHOD:

-/
theorem proof_gap_exercise_661_1
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  : Set.MapsTo f (Set.Ioi x₀) Set.univ := by
  sorry

/- Exercise 661, gap 2
PROOF GAP @2
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. f : RealSet → RealSet
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
5. N = floor(x_{0}) + 1
6. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
7. f : IntervalLoRo(x_{0}, +∞) → RealSet

GOAL:
forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| = frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1))

METHOD:

-/
theorem proof_gap_exercise_661_2
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  (h7 : Set.MapsTo f (Set.Ioi x₀) Set.univ)
  : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| = |g (n, x)| / exercise661Denom g x := by
  sorry

/- Exercise 661, gap 3
PROOF GAP @3
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. f : RealSet → RealSet
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
5. N = floor(x_{0}) + 1
6. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
7. f : IntervalLoRo(x_{0}, +∞) → RealSet
8. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| = frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1))

GOAL:
forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1)) < frac(1, floor(x))

METHOD:

-/
theorem proof_gap_exercise_661_3
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  (h7 : Set.MapsTo f (Set.Ioi x₀) Set.univ)
  (h8 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| = |g (n, x)| / exercise661Denom g x)
  : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x)| / exercise661Denom g x < 1 / (⌊x⌋ : ℤ) := by
  sorry

/- Exercise 661, gap 4
PROOF GAP @4
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. f : RealSet → RealSet
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
5. N = floor(x_{0}) + 1
6. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
7. f : IntervalLoRo(x_{0}, +∞) → RealSet
8. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| = frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1))
9. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1)) < frac(1, floor(x))

GOAL:
forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| < frac(1, floor(x))

METHOD:

-/
theorem proof_gap_exercise_661_4
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  (h7 : Set.MapsTo f (Set.Ioi x₀) Set.univ)
  (h8 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| = |g (n, x)| / exercise661Denom g x)
  (h9 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x)| / exercise661Denom g x < 1 / (⌊x⌋ : ℤ))
  : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| < 1 / (⌊x⌋ : ℤ) := by
  sorry

/- Exercise 661, gap 5
PROOF GAP @5
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. f : RealSet → RealSet
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
5. N = floor(x_{0}) + 1
6. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
7. f : IntervalLoRo(x_{0}, +∞) → RealSet
8. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| = frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1))
9. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1)) < frac(1, floor(x))
10. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| < frac(1, floor(x))

GOAL:
forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(1, floor(x))) = 0

METHOD:

-/
theorem proof_gap_exercise_661_5
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  (h7 : Set.MapsTo f (Set.Ioi x₀) Set.univ)
  (h8 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| = |g (n, x)| / exercise661Denom g x)
  (h9 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x)| / exercise661Denom g x < 1 / (⌊x⌋ : ℤ))
  (h10 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| < 1 / (⌊x⌋ : ℤ))
  : ∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => (1 : ℝ) / (⌊x⌋ : ℤ)) atTop (𝓝 0) := by
  sorry

/- Exercise 661, gap 6
PROOF GAP @6
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. f : RealSet → RealSet
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
5. N = floor(x_{0}) + 1
6. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
7. f : IntervalLoRo(x_{0}, +∞) → RealSet
8. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| = frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1))
9. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1)) < frac(1, floor(x))
10. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| < frac(1, floor(x))
11. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(1, floor(x))) = 0

GOAL:
forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(g(n, x), f(x))) = 0

METHOD:

-/
theorem proof_gap_exercise_661_6
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  (h7 : Set.MapsTo f (Set.Ioi x₀) Set.univ)
  (h8 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| = |g (n, x)| / exercise661Denom g x)
  (h9 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x)| / exercise661Denom g x < 1 / (⌊x⌋ : ℤ))
  (h10 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| < 1 / (⌊x⌋ : ℤ))
  (h11 : ∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => (1 : ℝ) / (⌊x⌋ : ℤ)) atTop (𝓝 0))
  : ∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => g (n, x) / f x) atTop (𝓝 0) := by
  sorry

/- Exercise 661, gap 7
PROOF GAP @7
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. f : RealSet → RealSet
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
5. N = floor(x_{0}) + 1
6. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
7. f : IntervalLoRo(x_{0}, +∞) → RealSet
8. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| = frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1))
9. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1)) < frac(1, floor(x))
10. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| < frac(1, floor(x))
11. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(1, floor(x))) = 0
12. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(g(n, x), f(x))) = 0

GOAL:
exists (f), f : RealSet → RealSet ∧ f : IntervalLoRo(x_{0}, +∞) → RealSet ∧ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(g(n, x), f(x))) = 0)

METHOD:

-/
theorem proof_gap_exercise_661_7
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  (h7 : Set.MapsTo f (Set.Ioi x₀) Set.univ)
  (h8 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| = |g (n, x)| / exercise661Denom g x)
  (h9 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x)| / exercise661Denom g x < 1 / (⌊x⌋ : ℤ))
  (h10 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| < 1 / (⌊x⌋ : ℤ))
  (h11 : ∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => (1 : ℝ) / (⌊x⌋ : ℤ)) atTop (𝓝 0))
  (h12 : ∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => g (n, x) / f x) atTop (𝓝 0))
  : ∃ F : ℝ → ℝ, Set.MapsTo F (Set.Ioi x₀) Set.univ ∧ (∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => g (n, x) / F x) atTop (𝓝 0)) := by
  sorry

/- Exercise 661, gap 8
PROOF GAP @8
ASSUM:
1. x_{0} ∈ RealSet
2. g : CartesianProd(NonNegIntegerSet, RealSet) → RealSet
3. f : RealSet → RealSet
4. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ g(n) : IntervalLoRo(x_{0}, +∞) → RealSet
5. N = floor(x_{0}) + 1
6. f = (fun x [x ∈ RealSet ∧ x ∈ IntervalLoRo(x_{0}, +∞)] . cases{ floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1) if x ≥ N; 0 if x_{0} < x ∧ x < N })
7. f : IntervalLoRo(x_{0}, +∞) → RealSet
8. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| = frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1))
9. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ frac(|g(n, x)|, floor(x) * ((sum_{ k = 1 }^{ floor(x) } (|g(k, x)|)) + 1)) < frac(1, floor(x))
10. forall (n) (x), n ∈ NonNegIntegerSet ∧ x ∈ RealSet ∧ x > max(N, n) ∧ n ∈ PosIntegerSet ⇒ |frac(g(n, x), f(x))| < frac(1, floor(x))
11. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(1, floor(x))) = 0
12. forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(g(n, x), f(x))) = 0
13. exists (f), f : RealSet → RealSet ∧ f : IntervalLoRo(x_{0}, +∞) → RealSet ∧ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(g(n, x), f(x))) = 0)

GOAL:
exists (f), f : RealSet → RealSet ∧ f : IntervalLoRo(x_{0}, +∞) → RealSet ∧ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ lim_{ x → +∞ } (frac(g(n, x), f(x))) = 0)

METHOD:

-/
theorem proof_gap_exercise_661_8
  (x₀ : ℝ) (g : ℕ × ℝ → ℝ) (f : ℝ → ℝ) (N : ℤ)
  (h1 : x₀ ∈ (Set.univ : Set ℝ))
  (h4 : ∀ n : ℕ, 0 < n → Set.MapsTo (fun x => g (n, x)) (Set.Ioi x₀) Set.univ)
  (h5 : N = ⌊x₀⌋ + 1)
  (h6 : Set.EqOn f (fun x => if (N : ℝ) ≤ x then exercise661Denom g x else 0) (Set.Ioi x₀))
  (h7 : Set.MapsTo f (Set.Ioi x₀) Set.univ)
  (h8 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| = |g (n, x)| / exercise661Denom g x)
  (h9 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x)| / exercise661Denom g x < 1 / (⌊x⌋ : ℤ))
  (h10 : ∀ (n : ℕ) (x : ℝ), x > max (N : ℝ) (n : ℝ) ∧ 0 < n → |g (n, x) / f x| < 1 / (⌊x⌋ : ℤ))
  (h11 : ∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => (1 : ℝ) / (⌊x⌋ : ℤ)) atTop (𝓝 0))
  (h12 : ∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => g (n, x) / f x) atTop (𝓝 0))
  (h13 : ∃ F : ℝ → ℝ, Set.MapsTo F (Set.Ioi x₀) Set.univ ∧ (∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => g (n, x) / F x) atTop (𝓝 0)))
  : ∃ F : ℝ → ℝ, Set.MapsTo F (Set.Ioi x₀) Set.univ ∧ (∀ n : ℕ, 0 < n → Tendsto (fun x : ℝ => g (n, x) / F x) atTop (𝓝 0)) := by
  sorry
