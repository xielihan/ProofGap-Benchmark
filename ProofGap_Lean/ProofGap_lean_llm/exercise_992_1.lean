import Mathlib

open scoped Topology
open Filter

/- The original exercise explicitly requires that x^n be defined.
For gaps 1-5 a total f represents its restriction to exercise992Domain n;
all evaluations, limits and continuity statements use that domain.
Negative bases are allowed exactly for rational exponents with odd reduced
 denominator. The separate value f 0 = 0 adds 0 to the domain for every n.
The zero branch of exercise992Power is never observed outside this domain.
Gap 4's missing positivity and gap 6's absolute-value formula are preserved. -/
def exercise992Domain (n : ℝ) : Set ℝ :=
  {x | 0 ≤ x ∨ ∃ r : ℚ, (r : ℝ) = n ∧ Odd r.den}

noncomputable def exercise992Power (x n : ℝ) : ℝ := by
  classical
  exact if 0 ≤ x then Real.rpow x n
    else if h : ∃ r : ℚ, (r : ℝ) = n ∧ Odd r.den then
      (-1 : ℝ) ^ (Classical.choose h).num * Real.rpow |x| n
    else 0

/- Exercise 992_1, gap 1
SHA-256: e4a14747ce7170d279e07d42fd790de46c58076cab975ddaee8eb3fcb4c53cd2
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. n ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = x^{n} * sin(frac(1, x))
4. f(0) = 0
5. forall (x), x ∈ RealSet

GOAL:
n ∈ PosRealSet ⇒ lim_{ x → 0 } (x^{n} * sin(frac(1, x))) = 0

METHOD:

-/
theorem proof_gap_exercise_992_1_1
  (f : ℝ → ℝ) (n : ℝ)
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → x ∈ exercise992Domain n → f x = exercise992Power x n * Real.sin (1 / x))
  (h4 : f 0 = 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ))
  : 0 < n → Tendsto (fun x : ℝ => exercise992Power x n * Real.sin (1 / x)) (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 0) := by
  sorry

/- Exercise 992_1, gap 2
SHA-256: df3b423fd6de0069662f34549b49ef8a75b552dfde8056a6b10a2e65ab8840d4
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. n ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = x^{n} * sin(frac(1, x))
4. f(0) = 0
5. forall (x), x ∈ RealSet
6. n ∈ PosRealSet ⇒ lim_{ x → 0 } (x^{n} * sin(frac(1, x))) = 0

GOAL:
n ∈ PosRealSet ⇒ lim_{ x → 0 } (f(x)) = f(0)

METHOD:

-/
theorem proof_gap_exercise_992_1_2
  (f : ℝ → ℝ) (n : ℝ)
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → x ∈ exercise992Domain n → f x = exercise992Power x n * Real.sin (1 / x))
  (h4 : f 0 = 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ))
  (h6 : 0 < n → Tendsto (fun x : ℝ => exercise992Power x n * Real.sin (1 / x)) (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 0))
  : 0 < n → Tendsto f (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 (f 0)) := by
  sorry

/- Exercise 992_1, gap 3
SHA-256: 9703868bb335e0f327e80b8a73d7dca734659278ca8be3cdb43d370a6b75641f
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. n ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = x^{n} * sin(frac(1, x))
4. f(0) = 0
5. forall (x), x ∈ RealSet
6. n ∈ PosRealSet ⇒ lim_{ x → 0 } (x^{n} * sin(frac(1, x))) = 0
7. n ∈ PosRealSet ⇒ lim_{ x → 0 } (f(x)) = f(0)

GOAL:
n ∈ PosRealSet ⇒ ContinuousFuncAt(f, 0)

METHOD:

-/
theorem proof_gap_exercise_992_1_3
  (f : ℝ → ℝ) (n : ℝ)
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → x ∈ exercise992Domain n → f x = exercise992Power x n * Real.sin (1 / x))
  (h4 : f 0 = 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ))
  (h6 : 0 < n → Tendsto (fun x : ℝ => exercise992Power x n * Real.sin (1 / x)) (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 0))
  (h7 : 0 < n → Tendsto f (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 (f 0)))
  : 0 < n → ContinuousWithinAt f (exercise992Domain n) 0 := by
  sorry

/- Exercise 992_1, gap 4
SHA-256: 4fbc7ed3fefb37d44498d0e7b5abc4cdd4504d52f3553d6e1debadaa08bf2ec8
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. n ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = x^{n} * sin(frac(1, x))
4. f(0) = 0
5. forall (x), x ∈ RealSet
6. n ∈ PosRealSet ⇒ lim_{ x → 0 } (x^{n} * sin(frac(1, x))) = 0
7. n ∈ PosRealSet ⇒ lim_{ x → 0 } (f(x)) = f(0)
8. n ∈ PosRealSet ⇒ ContinuousFuncAt(f, 0)

GOAL:
(exists (p) (q), q ∈ IntegerSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ n = frac(p, q) ∧ gcd(p, q) = 1 ∧ Even(q)) ⇒ lim_{ x → 0^+ } (x^{n} * sin(frac(1, x))) = 0

METHOD:

-/
theorem proof_gap_exercise_992_1_4
  (f : ℝ → ℝ) (n : ℝ)
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → x ∈ exercise992Domain n → f x = exercise992Power x n * Real.sin (1 / x))
  (h4 : f 0 = 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ))
  (h6 : 0 < n → Tendsto (fun x : ℝ => exercise992Power x n * Real.sin (1 / x)) (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 0))
  (h7 : 0 < n → Tendsto f (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 (f 0)))
  (h8 : 0 < n → ContinuousWithinAt f (exercise992Domain n) 0)
  : (∃ p q : ℤ, q ∈ (Set.univ : Set ℤ) ∧ p ∈ (Set.univ : Set ℤ) ∧ 0 < q ∧ n = (p : ℝ) / (q : ℝ) ∧ Int.gcd p q = 1 ∧ Even q) → Tendsto (fun x : ℝ => exercise992Power x n * Real.sin (1 / x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry

/- Exercise 992_1, gap 5
SHA-256: 69817ba08c80c6b8c62599eab5198e99bf4fb563d4ff6e5ff39b590d3524c7a9
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. n ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = x^{n} * sin(frac(1, x))
4. f(0) = 0
5. forall (x), x ∈ RealSet
6. n ∈ PosRealSet ⇒ lim_{ x → 0 } (x^{n} * sin(frac(1, x))) = 0
7. n ∈ PosRealSet ⇒ lim_{ x → 0 } (f(x)) = f(0)
8. n ∈ PosRealSet ⇒ ContinuousFuncAt(f, 0)
9. (exists (p) (q), q ∈ IntegerSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ n = frac(p, q) ∧ gcd(p, q) = 1 ∧ Even(q)) ⇒ lim_{ x → 0^+ } (x^{n} * sin(frac(1, x))) = 0

GOAL:
(exists (p) (q), q ∈ IntegerSet ∧ p ∈ IntegerSet ∧ q ∈ PosIntegerSet ∧ n = frac(p, q) ∧ gcd(p, q) = 1 ∧ Even(q)) ⇒ lim_{ x → 0^+ } (f(x)) = f(0)

METHOD:

-/
theorem proof_gap_exercise_992_1_5
  (f : ℝ → ℝ) (n : ℝ)
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → x ∈ exercise992Domain n → f x = exercise992Power x n * Real.sin (1 / x))
  (h4 : f 0 = 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ))
  (h6 : 0 < n → Tendsto (fun x : ℝ => exercise992Power x n * Real.sin (1 / x)) (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 0))
  (h7 : 0 < n → Tendsto f (𝓝[exercise992Domain n \ {0}] (0 : ℝ)) (𝓝 (f 0)))
  (h8 : 0 < n → ContinuousWithinAt f (exercise992Domain n) 0)
  (h9 : (∃ p q : ℤ, q ∈ (Set.univ : Set ℤ) ∧ p ∈ (Set.univ : Set ℤ) ∧ 0 < q ∧ n = (p : ℝ) / (q : ℝ) ∧ Int.gcd p q = 1 ∧ Even q) → Tendsto (fun x : ℝ => exercise992Power x n * Real.sin (1 / x)) (𝓝[>] (0 : ℝ)) (𝓝 0))
  : (∃ p q : ℤ, q ∈ (Set.univ : Set ℤ) ∧ p ∈ (Set.univ : Set ℤ) ∧ 0 < q ∧ n = (p : ℝ) / (q : ℝ) ∧ Int.gcd p q = 1 ∧ Even q) → Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  sorry

/- Exercise 992_1, gap 6
SHA-256: 4d950d16af2b89b91e49d11cc88f2b087d1a6bc6a2b7466ac3435727747bbc2e
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. n ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 0 ⇒ f(x) = |x|^{n} * sin(frac(1, x))
4. f(0) = 0
5. forall (x), x ∈ RealSet
6. n ∈ PosRealSet ⇒ lim_{ x → 0 } (|x|^{n} * sin(frac(1, x))) = 0
7. n ∈ PosRealSet ⇒ lim_{ x → 0 } (f(x)) = f(0)
8. n ∈ PosRealSet ⇒ ContinuousFuncAt(f, 0)
9. (exists (p) (q), q ∈ IntegerSet ∧ p ∈ PosIntegerSet ∧ q ∈ PosIntegerSet ∧ n = frac(p, q) ∧ gcd(p, q) = 1 ∧ Even(q)) ⇒ lim_{ x → 0^+ } (|x|^{n} * sin(frac(1, x))) = 0
10. (exists (p) (q), q ∈ IntegerSet ∧ p ∈ PosIntegerSet ∧ q ∈ PosIntegerSet ∧ n = frac(p, q) ∧ gcd(p, q) = 1 ∧ Even(q)) ⇒ lim_{ x → 0^+ } (f(x)) = f(0)
GOAL:
n ∈ PosRealSet ⇔ ContinuousFuncAt(f, 0)

METHOD:

-/
theorem proof_gap_exercise_992_1_6
  (f : ℝ → ℝ) (n : ℝ)
  (h2 : n ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 0 → f x = Real.rpow |x| n * Real.sin (1 / x))
  (h4 : f 0 = 0)
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ))
  (h6 : 0 < n → Tendsto (fun x : ℝ => Real.rpow |x| n * Real.sin (1 / x)) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  (h7 : 0 < n → Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 (f 0)))
  (h8 : 0 < n → ContinuousAt f 0)
  (h9 : (∃ p q : ℤ, q ∈ (Set.univ : Set ℤ) ∧ 0 < p ∧ 0 < q ∧ n = (p : ℝ) / (q : ℝ) ∧ Int.gcd p q = 1 ∧ Even q) → Tendsto (fun x : ℝ => Real.rpow |x| n * Real.sin (1 / x)) (𝓝[>] (0 : ℝ)) (𝓝 0))
  (h10 : (∃ p q : ℤ, q ∈ (Set.univ : Set ℤ) ∧ 0 < p ∧ 0 < q ∧ n = (p : ℝ) / (q : ℝ) ∧ Int.gcd p q = 1 ∧ Even q) → Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)))
  : 0 < n ↔ ContinuousAt f 0 := by
  sorry

