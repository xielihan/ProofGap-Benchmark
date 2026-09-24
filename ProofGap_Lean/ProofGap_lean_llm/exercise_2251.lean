import Mathlib

open scoped Interval

namespace Exercise2251

-- Defined(f,A) means each input in A has an output in the graph of f.
-- Total ℝ → ℝ functions necessarily satisfy this predicate; the source's
-- negations are deliberately preserved, with their inconsistency in the review.
def DefinedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ y : ℝ, f x = y

-- The source uses the real cube-root convention: x^(2/3) = |x|^(2/3).
-- All integrators are the identity, so f(x) dx becomes the interval integral of f.
-- Only the 25 main theorem proofs use sorry.

/- Exercise 2251, gap 1
PROOF GAP @1
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
GOAL:
DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2

METHOD:

-/
theorem proof_gap_exercise_2251_1
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2 := by
  sorry

/- Exercise 2251, gap 2
PROOF GAP @2
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2

GOAL:
phi_{1}(-1) = phi_{1}(1)

METHOD:
[@method 根据 phi_{1}(x) = x^{frac(2, 3)} @]
-/
theorem proof_gap_exercise_2251_2
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  : phi1 (-1) = phi1 1 := by
  sorry

/- Exercise 2251, gap 3
PROOF GAP @3
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)

GOAL:
phi_{1}(1) = 1

METHOD:
[@method 根据 phi_{1}(x) = x^{frac(2, 3)} @]
-/
theorem proof_gap_exercise_2251_3
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  : phi1 1 = 1 := by
  sorry

/- Exercise 2251, gap 4
PROOF GAP @4
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1

GOAL:
phi_{1}(-1) = 1

METHOD:
[@method 根据 phi_{1}(x) = x^{frac(2, 3)} @]
-/
theorem proof_gap_exercise_2251_4
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  : phi1 (-1) = 1 := by
  sorry

/- Exercise 2251, gap 5
PROOF GAP @5
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1

GOAL:
¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))

METHOD:

-/
theorem proof_gap_exercise_2251_5
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1) := by
  sorry

/- Exercise 2251, gap 6
PROOF GAP @6
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))

GOAL:
forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})

METHOD:

-/
theorem proof_gap_exercise_2251_6
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ) := by
  sorry

/- Exercise 2251, gap 7
PROOF GAP @7
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})

GOAL:
¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))

METHOD:

-/
theorem proof_gap_exercise_2251_7
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)) := by
  sorry

/- Exercise 2251, gap 8
PROOF GAP @8
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))

GOAL:
DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0

METHOD:

-/
theorem proof_gap_exercise_2251_8
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0 := by
  sorry

/- Exercise 2251, gap 9
PROOF GAP @9
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0

GOAL:
frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0

METHOD:

-/
theorem proof_gap_exercise_2251_9
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0 := by
  sorry

/- Exercise 2251, gap 10
PROOF GAP @10
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0

GOAL:
DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})

METHOD:

-/
theorem proof_gap_exercise_2251_10
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) := by
  sorry

/- Exercise 2251, gap 11
PROOF GAP @11
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})

GOAL:
((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)

METHOD:

-/
theorem proof_gap_exercise_2251_11
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2 := by
  sorry

/- Exercise 2251, gap 12
PROOF GAP @12
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)

GOAL:
DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)

METHOD:

-/
theorem proof_gap_exercise_2251_12
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2 := by
  sorry

/- Exercise 2251, gap 13
PROOF GAP @13
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)

GOAL:
0 ∈ [-1, 1]

METHOD:

-/
theorem proof_gap_exercise_2251_13
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  sorry

/- Exercise 2251, gap 14
PROOF GAP @14
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]

GOAL:
¬Defined(phi_{2}, { 0 })

METHOD:

-/
theorem proof_gap_exercise_2251_14
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  : ¬DefinedOn phi2 ({0} : Set ℝ) := by
  sorry

/- Exercise 2251, gap 15
PROOF GAP @15
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })

GOAL:
¬ContinuousFuncAt(phi_{2}, 0)

METHOD:

-/
theorem proof_gap_exercise_2251_15
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  : ¬ContinuousAt phi2 0 := by
  sorry

/- Exercise 2251, gap 16
PROOF GAP @16
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)

GOAL:
DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))

METHOD:

-/
theorem proof_gap_exercise_2251_16
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) := by
  sorry

/- Exercise 2251, gap 17
PROOF GAP @17
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))

GOAL:
DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0

METHOD:

-/
theorem proof_gap_exercise_2251_17
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0 := by
  sorry

/- Exercise 2251, gap 18
PROOF GAP @18
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0

GOAL:
frac(π, 2) ∈ [0, π]

METHOD:

-/
theorem proof_gap_exercise_2251_18
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
  sorry

/- Exercise 2251, gap 19
PROOF GAP @19
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0
24. frac(π, 2) ∈ [0, π]

GOAL:
¬Defined(phi_{3}, { frac(π, 2) })

METHOD:

-/
theorem proof_gap_exercise_2251_19
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  (h24 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi)
  : ¬DefinedOn phi3 ({Real.pi / 2} : Set ℝ) := by
  sorry

/- Exercise 2251, gap 20
PROOF GAP @20
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0
24. frac(π, 2) ∈ [0, π]
25. ¬Defined(phi_{3}, { frac(π, 2) })

GOAL:
¬ContinuousFuncAt(phi_{3}, frac(π, 2))

METHOD:

-/
theorem proof_gap_exercise_2251_20
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  (h24 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi)
  (h25 : ¬DefinedOn phi3 ({Real.pi / 2} : Set ℝ))
  : ¬ContinuousAt phi3 (Real.pi / 2) := by
  sorry

/- Exercise 2251, gap 21
PROOF GAP @21
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ∈ [0, π] ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0
24. frac(π, 2) ∈ [0, π]
25. ¬Defined(phi_{3}, { frac(π, 2) })
26. ¬ContinuousFuncAt(phi_{3}, frac(π, 2))

GOAL:
DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ ((fun x [x ∈ RealSet] . frac(1, sqrtn(2, 2)) * arctan(sqrtn(2, 2) * tan(x)))|_{0}^{π})

METHOD:

-/
theorem proof_gap_exercise_2251_21
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) Real.pi ∧ x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  (h24 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi)
  (h25 : ¬DefinedOn phi3 ({Real.pi / 2} : Set ℝ))
  (h26 : ¬ContinuousAt phi3 (Real.pi / 2))
  : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) ≠ ((fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) Real.pi - (fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) 0) := by
  sorry

/- Exercise 2251, gap 22
PROOF GAP @22
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0
24. frac(π, 2) ∈ [0, π]
25. ¬Defined(phi_{3}, { frac(π, 2) })
26. ¬ContinuousFuncAt(phi_{3}, frac(π, 2))
27. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ ((fun x [x ∈ RealSet] . frac(1, sqrtn(2, 2)) * arctan(sqrtn(2, 2) * tan(x)))|_{0}^{π})

GOAL:
¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))

METHOD:

-/
theorem proof_gap_exercise_2251_22
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  (h24 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi)
  (h25 : ¬DefinedOn phi3 ({Real.pi / 2} : Set ℝ))
  (h26 : ¬ContinuousAt phi3 (Real.pi / 2))
  (h27 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) ≠ ((fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) Real.pi - (fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) 0))
  : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1) := by
  sorry

/- Exercise 2251, gap 23
PROOF GAP @23
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0
24. frac(π, 2) ∈ [0, π]
25. ¬Defined(phi_{3}, { frac(π, 2) })
26. ¬ContinuousFuncAt(phi_{3}, frac(π, 2))
27. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ ((fun x [x ∈ RealSet] . frac(1, sqrtn(2, 2)) * arctan(sqrtn(2, 2) * tan(x)))|_{0}^{π})
28. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))

GOAL:
¬ContinuousFuncAt(phi_{2}, 0)

METHOD:

-/
theorem proof_gap_exercise_2251_23
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  (h24 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi)
  (h25 : ¬DefinedOn phi3 ({Real.pi / 2} : Set ℝ))
  (h26 : ¬ContinuousAt phi3 (Real.pi / 2))
  (h27 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) ≠ ((fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) Real.pi - (fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) 0))
  (h28 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  : ¬ContinuousAt phi2 0 := by
  sorry

/- Exercise 2251, gap 24
PROOF GAP @24
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0
24. frac(π, 2) ∈ [0, π]
25. ¬Defined(phi_{3}, { frac(π, 2) })
26. ¬ContinuousFuncAt(phi_{3}, frac(π, 2))
27. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ ((fun x [x ∈ RealSet] . frac(1, sqrtn(2, 2)) * arctan(sqrtn(2, 2) * tan(x)))|_{0}^{π})
28. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
29. ¬ContinuousFuncAt(phi_{2}, 0)

GOAL:
¬ContinuousFuncAt(phi_{3}, frac(π, 2))

METHOD:

-/
theorem proof_gap_exercise_2251_24
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  (h24 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi)
  (h25 : ¬DefinedOn phi3 ({Real.pi / 2} : Set ℝ))
  (h26 : ¬ContinuousAt phi3 (Real.pi / 2))
  (h27 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) ≠ ((fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) Real.pi - (fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) 0))
  (h28 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h29 : ¬ContinuousAt phi2 0)
  : ¬ContinuousAt phi3 (Real.pi / 2) := by
  sorry

/- Exercise 2251, gap 25
PROOF GAP @25
ASSUM:
1. phi_{1} : RealSet → RealSet
2. phi_{2} : RealSet → RealSet
3. phi_{3} : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x ∈ [-1, 1] ⇒ phi_{1}(x) = x^{frac(2, 3)}
5. forall (t), t ∈ RealSet ∧ t ≠ 0 ⇒ phi_{2}(t) = frac(1, t)
6. forall (x), x ∈ RealSet ∧ x ≠ frac(π, 2) ⇒ phi_{3}(x) = tan(x)
7. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) = 2
8. phi_{1}(-1) = phi_{1}(1)
9. phi_{1}(1) = 1
10. phi_{1}(-1) = 1
11. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
12. forall (x), x ∈ RealSet ⇒ (forall (t), t ∈ RealSet ∧ phi_{1}(x) = t ⇒ x = t^{frac(3, 2)} ∨ x = -t^{frac(3, 2)})
13. ¬(exists (psi), psi : RealSet → RealSet ∧ (forall (t) (x), t ∈ RealSet ∧ x ∈ RealSet ∧ t ∈ [0, 1] ∧ x ∈ [-1, 1] ⇒ (phi_{1}(x) = t ⇔ x = psi(t))))
14. DefInt(-1, 1, diff(fun x [x ∈ RealSet] . x)) ≠ 0
15. frac(3, 2) * DefInt(1, 1, (fun t [t ∈ RealSet] . t^{frac(1, 2)}) * diff(fun t [t ∈ RealSet] . t)) = 0
16. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1})
17. ((fun x [x ∈ RealSet] . arctan(x))|_{-1}^{1}) = frac(π, 2)
18. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
19. 0 ∈ [-1, 1]
20. ¬Defined(phi_{2}, { 0 })
21. ¬ContinuousFuncAt(phi_{2}, 0)
22. DefInt(-1, 1, (fun x [x ∈ RealSet] . frac(1, 1 + x^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ -DefInt(-1, 1, (fun t [t ∈ RealSet] . frac(1, 1 + t^{2})) * diff(fun t [t ∈ RealSet] . t))
23. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) > 0
24. frac(π, 2) ∈ [0, π]
25. ¬Defined(phi_{3}, { frac(π, 2) })
26. ¬ContinuousFuncAt(phi_{3}, frac(π, 2))
27. DefInt(0, π, (fun x [x ∈ RealSet] . frac(1, 1 + sin(x)^{2})) * diff(fun x [x ∈ RealSet] . x)) ≠ ((fun x [x ∈ RealSet] . frac(1, sqrtn(2, 2)) * arctan(sqrtn(2, 2) * tan(x)))|_{0}^{π})
28. ¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1]))
29. ¬ContinuousFuncAt(phi_{2}, 0)
30. ¬ContinuousFuncAt(phi_{3}, frac(π, 2))

GOAL:
¬InjectiveFunc(RestrictFunc(phi_{1}, [-1, 1])) ∧ ¬ContinuousFuncAt(phi_{2}, 0) ∧ ¬ContinuousFuncAt(phi_{3}, frac(π, 2))

METHOD:

-/
theorem proof_gap_exercise_2251_25
  (phi1 phi2 phi3 : ℝ → ℝ)
  (h4 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → phi1 x = Real.rpow |x| (2 / 3 : ℝ))
  (h5 : ∀ t : ℝ, t ≠ 0 → phi2 t = 1 / t)
  (h6 : ∀ x : ℝ, x ≠ Real.pi / 2 → phi3 x = Real.tan x)
  (h7 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) = 2)
  (h8 : phi1 (-1) = phi1 1)
  (h9 : phi1 1 = 1)
  (h10 : phi1 (-1) = 1)
  (h11 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h12 : ∀ x : ℝ, ∀ t : ℝ, phi1 x = t → x = Real.rpow t (3 / 2 : ℝ) ∨ x = -Real.rpow t (3 / 2 : ℝ))
  (h13 : ¬(∃ psi : ℝ → ℝ, ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ Set.Icc (-1 : ℝ) 1 → (phi1 x = t ↔ x = psi t)))
  (h14 : (∫ x : ℝ in (-1)..1, (1 : ℝ)) ≠ 0)
  (h15 : (3 / 2 : ℝ) * (∫ t : ℝ in (1)..1, Real.rpow t (1 / 2 : ℝ)) = 0)
  (h16 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)))
  (h17 : (Real.arctan (1 : ℝ) - Real.arctan (-1 : ℝ)) = Real.pi / 2)
  (h18 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) = Real.pi / 2)
  (h19 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  (h20 : ¬DefinedOn phi2 ({0} : Set ℝ))
  (h21 : ¬ContinuousAt phi2 0)
  (h22 : (∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))) ≠ -(∫ x : ℝ in (-1)..1, 1 / (1 + x ^ (2 : ℕ))))
  (h23 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) > 0)
  (h24 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi)
  (h25 : ¬DefinedOn phi3 ({Real.pi / 2} : Set ℝ))
  (h26 : ¬ContinuousAt phi3 (Real.pi / 2))
  (h27 : (∫ x : ℝ in (0)..Real.pi, 1 / (1 + Real.sin x ^ (2 : ℕ))) ≠ ((fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) Real.pi - (fun x : ℝ => 1 / Real.sqrt 2 * Real.arctan (Real.sqrt 2 * Real.tan x)) 0))
  (h28 : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1))
  (h29 : ¬ContinuousAt phi2 0)
  (h30 : ¬ContinuousAt phi3 (Real.pi / 2))
  : ¬Set.InjOn phi1 (Set.Icc (-1 : ℝ) 1) ∧ ¬ContinuousAt phi2 0 ∧ ¬ContinuousAt phi3 (Real.pi / 2) := by
  sorry

end Exercise2251
