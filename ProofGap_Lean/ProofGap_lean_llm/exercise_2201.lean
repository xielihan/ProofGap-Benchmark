import Mathlib

open scoped BigOperators Topology
open Filter

namespace Exercise2201

noncomputable def dirichletSign (x : ℝ) : ℝ :=
  by
    classical
    exact if ∃ q : ℚ, (q : ℝ) = x then 1 else -1

-- Definition 227: supremum of all absolute pairwise differences.
noncomputable def oscillation (f : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ s, ∃ v ∈ s, r = |f u - f v|}

noncomputable def oscSum (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, oscillation f (Set.Icc (x i) (x (i + 1))) * (x (i + 1) - x i)

-- Riemann integrability by the bounded-function Darboux oscillation criterion.
-- These partition conditions belong to the definition of integrability only;
-- they are deliberately NOT added to the source's arbitrary sequences below.
def riemannIntegrable (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∃ M : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ M) ∧
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ x : ℕ → ℝ,
    0 < n ∧ x 0 = a ∧ x n = b ∧
    (∀ i : ℕ, i < n → x i < x (i + 1)) ∧ oscSum f x n < ε

-- Definition 267 uses ambient continuity at each point of the set.
def continuousAtEveryPoint (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ t ∈ Set.Icc a b, ContinuousAt f t

end Exercise2201

open Exercise2201

/- Exercise 2201, gap 1
SHA-256: 452c63e86ed43cc61ab4e7c27dae28c87f4183642b6dc636a787f3abc75e65a1
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1

METHOD:

-/
theorem proof_gap_exercise_2201_1
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1 := by sorry

/- Exercise 2201, gap 2
SHA-256: 2ead1e64d8119a0a37d90ee8efd0b13d34534d986425b097e21c209a9bdb8df1
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })
5. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1

GOAL:
ContinuousFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])

METHOD:

-/
theorem proof_gap_exercise_2201_2
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  (h5 : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1)
  : continuousAtEveryPoint (fun t => |f t|) a b := by sorry

/- Exercise 2201, gap 3
SHA-256: c2a175ade7e7b6485a7a7cdfd2101d3eb5feccfb8b5ea8b5873274d8d45eeb55
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })
5. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1
6. ContinuousFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])

GOAL:
IntegrableFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])

METHOD:

-/
theorem proof_gap_exercise_2201_3
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  (h5 : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1)
  (h6 : continuousAtEveryPoint (fun t => |f t|) a b)
  : riemannIntegrable (fun t => |f t|) a b := by sorry

/- Exercise 2201, gap 4
SHA-256: 0d02da1da42554d327cc1cffe8cbb9d037ceb3268efda588bae1160d0b00d2ab
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })
5. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1
6. ContinuousFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
7. IntegrableFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])

GOAL:
forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i < n ⇒ OscillationOn(f, [x(i), x(i + 1)]) = 2))

METHOD:

-/
theorem proof_gap_exercise_2201_4
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  (h5 : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1)
  (h6 : continuousAtEveryPoint (fun t => |f t|) a b)
  (h7 : riemannIntegrable (fun t => |f t|) a b)
  : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) → oscillation f (Set.Icc (x i.toNat) (x (i + 1).toNat)) = 2 := by sorry

/- Exercise 2201, gap 5
SHA-256: 39b82837551e3e557243c5f6ee1548284d28496dcfb968d366a6a954383daf66
PROOF GAP @5
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })
5. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1
6. ContinuousFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
7. IntegrableFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
8. forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i < n ⇒ OscillationOn(f, [x(i), x(i + 1)]) = 2))

GOAL:
forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ sum_{ i = 0 }^{ n - 1 } (OscillationOn(f, [x(i), x(i + 1)]) * (x(i + 1) - x(i))) = 2 * (b - a))

METHOD:

-/
theorem proof_gap_exercise_2201_5
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  (h5 : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1)
  (h6 : continuousAtEveryPoint (fun t => |f t|) a b)
  (h7 : riemannIntegrable (fun t => |f t|) a b)
  (h8 : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) → oscillation f (Set.Icc (x i.toNat) (x (i + 1).toNat)) = 2)
  : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → oscSum f x n = 2 * (b - a) := by sorry

/- Exercise 2201, gap 6
SHA-256: 9153f6dfdee8e1424a467e2d04f0cd73de634fd6bdc11368445ec473535483b9
PROOF GAP @6
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })
5. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1
6. ContinuousFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
7. IntegrableFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
8. forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i < n ⇒ OscillationOn(f, [x(i), x(i + 1)]) = 2))
9. forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ sum_{ i = 0 }^{ n - 1 } (OscillationOn(f, [x(i), x(i + 1)]) * (x(i + 1) - x(i))) = 2 * (b - a))

GOAL:
forall (x), x : NonNegIntegerSet → RealSet ⇒ ¬lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (OscillationOn(f, [x(i), x(i + 1)]) * (x(i + 1) - x(i)))) = 0

METHOD:

-/
theorem proof_gap_exercise_2201_6
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  (h5 : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1)
  (h6 : continuousAtEveryPoint (fun t => |f t|) a b)
  (h7 : riemannIntegrable (fun t => |f t|) a b)
  (h8 : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) → oscillation f (Set.Icc (x i.toNat) (x (i + 1).toNat)) = 2)
  (h9 : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → oscSum f x n = 2 * (b - a))
  : ∀ x : ℕ → ℝ, ¬ Tendsto (oscSum f x) atTop (𝓝 0) := by sorry

/- Exercise 2201, gap 7
SHA-256: 3062c095d5909266f32130146fb7f041686ed121da9d9bdc30dc1f3983f5dd48
PROOF GAP @7
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })
5. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1
6. ContinuousFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
7. IntegrableFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
8. forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i < n ⇒ OscillationOn(f, [x(i), x(i + 1)]) = 2))
9. forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ sum_{ i = 0 }^{ n - 1 } (OscillationOn(f, [x(i), x(i + 1)]) * (x(i + 1) - x(i))) = 2 * (b - a))
10. forall (x), x : NonNegIntegerSet → RealSet ⇒ ¬lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (OscillationOn(f, [x(i), x(i + 1)]) * (x(i + 1) - x(i)))) = 0

GOAL:
¬IntegrableFuncOn(f, [a, b])

METHOD:

-/
theorem proof_gap_exercise_2201_7
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  (h5 : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1)
  (h6 : continuousAtEveryPoint (fun t => |f t|) a b)
  (h7 : riemannIntegrable (fun t => |f t|) a b)
  (h8 : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) → oscillation f (Set.Icc (x i.toNat) (x (i + 1).toNat)) = 2)
  (h9 : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → oscSum f x n = 2 * (b - a))
  (h10 : ∀ x : ℕ → ℝ, ¬ Tendsto (oscSum f x) atTop (𝓝 0))
  : ¬ riemannIntegrable f a b := by sorry

/- Exercise 2201, gap 8
SHA-256: bf768f9d16bcfce8cfdc153ba0c39ad2d807c012d4700e760c4d4c76eb05091b
PROOF GAP @8
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. a < b
4. f = (fun x [x ∈ RealSet] . cases{ 1 if x ∈ RationalSet; -1 if x ∉ RationalSet })
5. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ⇒ |f(x)| = 1
6. ContinuousFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
7. IntegrableFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b])
8. forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i < n ⇒ OscillationOn(f, [x(i), x(i + 1)]) = 2))
9. forall (x), x : NonNegIntegerSet → RealSet ⇒ (forall (n), n ∈ NonNegIntegerSet ∧ n ∈ PosIntegerSet ⇒ sum_{ i = 0 }^{ n - 1 } (OscillationOn(f, [x(i), x(i + 1)]) * (x(i + 1) - x(i))) = 2 * (b - a))
10. forall (x), x : NonNegIntegerSet → RealSet ⇒ ¬lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (OscillationOn(f, [x(i), x(i + 1)]) * (x(i + 1) - x(i)))) = 0
11. ¬IntegrableFuncOn(f, [a, b])

GOAL:
¬(forall (f), f : RealSet → RealSet ∧ IntegrableFuncOn(fun x [x ∈ RealSet] . |f(x)|, [a, b]) ⇒ IntegrableFuncOn(f, [a, b]))

METHOD:

-/
theorem proof_gap_exercise_2201_8
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : a < b)
  (h4 : f = dirichletSign)
  (h5 : ∀ t : ℝ, t ∈ Set.Icc a b → |f t| = 1)
  (h6 : continuousAtEveryPoint (fun t => |f t|) a b)
  (h7 : riemannIntegrable (fun t => |f t|) a b)
  (h8 : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) → oscillation f (Set.Icc (x i.toNat) (x (i + 1).toNat)) = 2)
  (h9 : ∀ x : ℕ → ℝ, ∀ n : ℕ, 0 < n → oscSum f x n = 2 * (b - a))
  (h10 : ∀ x : ℕ → ℝ, ¬ Tendsto (oscSum f x) atTop (𝓝 0))
  (h11 : ¬ riemannIntegrable f a b)
  : ¬ (∀ g : ℝ → ℝ, riemannIntegrable (fun t => |g t|) a b → riemannIntegrable g a b) := by sorry

