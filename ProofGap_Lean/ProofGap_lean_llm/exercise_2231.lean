import Mathlib

-- Real-domain lambdas are total real functions. DefInt is oriented interval integration.
-- FunDeri(_, 1, 1) is the first derivative in the sole argument, not evaluation at 1.
-- In gaps 4 and 5 the original text supplies evaluation at a and b, respectively.

/- Exercise 2231, gap 1
SHA-256: a83acfc8b3d8562aa4e80ecdd7d483849bda757d5549bd648c0cf1c168b91e2b
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. x ∈ RealSet

GOAL:
ContinuousFunc(fun t [t ∈ RealSet] . sin(t^{2}))

METHOD:
-/
theorem proof_gap_exercise_2231_1
  (a b x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  : Continuous (fun t : ℝ => Real.sin (t ^ (2 : ℕ))) := by
  sorry

/- Exercise 2231, gap 2
SHA-256: 99fb912435a3436cd7cc1e0c021afc0518b7114799a7612d2d0bd92a1593d4b2
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. x ∈ RealSet
4. ContinuousFunc(fun t [t ∈ RealSet] . sin(t^{2}))

GOAL:
FunDeri(fun x [x ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = 0

METHOD:
-/
theorem proof_gap_exercise_2231_2
  (a b x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : Continuous (fun t : ℝ => Real.sin (t ^ (2 : ℕ))))
  : deriv (fun _u : ℝ => (∫ t in a..b, Real.sin (t ^ (2 : ℕ)))) = (0 : ℝ → ℝ) := by
  sorry

/- Exercise 2231, gap 3
SHA-256: a9d73cf7b635ef8937272b6349942be2d4d3762456bcb36847845e45a838334f
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. x ∈ RealSet
4. ContinuousFunc(fun t [t ∈ RealSet] . sin(t^{2}))
5. FunDeri(fun x [x ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = 0

GOAL:
FunDeri(fun a [a ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = -FunDeri(fun a [a ∈ RealSet] . DefInt(b, a, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1)

METHOD:
-/
theorem proof_gap_exercise_2231_3
  (a b x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : Continuous (fun t : ℝ => Real.sin (t ^ (2 : ℕ))))
  (h5 : deriv (fun _u : ℝ => (∫ t in a..b, Real.sin (t ^ (2 : ℕ)))) = (0 : ℝ → ℝ))
  : deriv (fun u : ℝ => (∫ t in u..b, Real.sin (t ^ (2 : ℕ)))) =
    -deriv (fun u : ℝ => (∫ t in b..u, Real.sin (t ^ (2 : ℕ)))) := by
  sorry

/- Exercise 2231, gap 4
SHA-256: 2239d31fab3b0ae30f9ea6557e5b0bb23bf193a4fafd77dcf3d4cdf6b3fc7ea6
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. x ∈ RealSet
4. ContinuousFunc(fun t [t ∈ RealSet] . sin(t^{2}))
5. FunDeri(fun x [x ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = 0
6. FunDeri(fun a [a ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = -FunDeri(fun a [a ∈ RealSet] . DefInt(b, a, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1)

GOAL:
-FunDeri(fun a [a ∈ RealSet] . DefInt(b, a, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = -sin(a^{2})

METHOD:
-/
theorem proof_gap_exercise_2231_4
  (a b x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : Continuous (fun t : ℝ => Real.sin (t ^ (2 : ℕ))))
  (h5 : deriv (fun _u : ℝ => (∫ t in a..b, Real.sin (t ^ (2 : ℕ)))) = (0 : ℝ → ℝ))
  (h6 : deriv (fun u : ℝ => (∫ t in u..b, Real.sin (t ^ (2 : ℕ)))) =
    -deriv (fun u : ℝ => (∫ t in b..u, Real.sin (t ^ (2 : ℕ)))))
  : -(deriv (fun u : ℝ => (∫ t in b..u, Real.sin (t ^ (2 : ℕ)))) a) =
    -Real.sin (a ^ (2 : ℕ)) := by
  sorry

/- Exercise 2231, gap 5
SHA-256: 35927b99bd89e88548fc1959e75e707b53f25d8e77ce022b5c38ba2d141045dc
PROOF GAP @5
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. x ∈ RealSet
4. ContinuousFunc(fun t [t ∈ RealSet] . sin(t^{2}))
5. FunDeri(fun x [x ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = 0
6. FunDeri(fun a [a ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = -FunDeri(fun a [a ∈ RealSet] . DefInt(b, a, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1)
7. -FunDeri(fun a [a ∈ RealSet] . DefInt(b, a, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = -sin(a^{2})

GOAL:
FunDeri(fun b [b ∈ RealSet] . DefInt(a, b, (fun t [t ∈ RealSet] . sin(t^{2})) * diff(fun t [t ∈ RealSet] . t)), 1, 1) = sin(b^{2})

METHOD:
-/
theorem proof_gap_exercise_2231_5
  (a b x : ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : Continuous (fun t : ℝ => Real.sin (t ^ (2 : ℕ))))
  (h5 : deriv (fun _u : ℝ => (∫ t in a..b, Real.sin (t ^ (2 : ℕ)))) = (0 : ℝ → ℝ))
  (h6 : deriv (fun u : ℝ => (∫ t in u..b, Real.sin (t ^ (2 : ℕ)))) =
    -deriv (fun u : ℝ => (∫ t in b..u, Real.sin (t ^ (2 : ℕ)))))
  (h7 : -(deriv (fun u : ℝ => (∫ t in b..u, Real.sin (t ^ (2 : ℕ)))) a) =
    -Real.sin (a ^ (2 : ℕ)))
  : deriv (fun u : ℝ => (∫ t in a..u, Real.sin (t ^ (2 : ℕ)))) b =
    Real.sin (b ^ (2 : ℕ)) := by
  sorry

