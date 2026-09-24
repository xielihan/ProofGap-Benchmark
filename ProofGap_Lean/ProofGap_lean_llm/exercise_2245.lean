import Mathlib

set_option linter.style.longLine false

-- The differential of a restricted function, as a field of continuous linear maps.
-- Only points of the closed source interval are compared; no extension outside it is used.
noncomputable def differential (f : ℝ → ℝ) : Set.Icc (-1 : ℝ) 1 → (ℝ →L[ℝ] ℝ) :=
  fun y => fderivWithin ℝ f (Set.Icc (-1 : ℝ) 1) y.val

/- Exercise 2245, gap 1
SHA-256: da7748130befc82356dd26902664131bff00fc3ea049faf422907af68db68159
PROOF GAP @1
ASSUM:
1. t : RealSet → RealSet

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ 5 - 4 * x > 0

METHOD:

-/
theorem proof_gap_exercise_2245_1
  (t : ℝ → ℝ)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → 5 - 4 * x > 0 := by
  sorry

/- Exercise 2245, gap 2
SHA-256: 16ad5f12894d82695a7350c045008c6d0980a051fe93d082f529b201c9d5f683
PROOF GAP @2
ASSUM:
1. t : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ 5 - 4 * x > 0

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ t(x) ∈ [1, 3]

METHOD:

-/
theorem proof_gap_exercise_2245_2
  (t : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → 5 - 4 * x > 0)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → t x ∈ Set.Icc (1 : ℝ) 3 := by
  sorry

/- Exercise 2245, gap 3
SHA-256: 5a79995579dcad48ab0026c6520113d680489db647d2e0b5b632c0b97133a95b
PROOF GAP @3
ASSUM:
1. t : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ 5 - 4 * x > 0
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ t(x) ∈ [1, 3]

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ x = frac(5 - t(x)^{2}, 4)

METHOD:

-/
theorem proof_gap_exercise_2245_3
  (t : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → 5 - 4 * x > 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → t x ∈ Set.Icc (1 : ℝ) 3)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → x = (5 - (t x)^2) / 4 := by
  sorry

/- Exercise 2245, gap 4
SHA-256: 48e04bf7498225c3fa05efbb0cf0371ddcc35d1cf5cf586d28f1536610c5114a
PROOF GAP @4
ASSUM:
1. t : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ 5 - 4 * x > 0
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ t(x) ∈ [1, 3]
4. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ x = frac(5 - t(x)^{2}, 4)

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x) = (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . -frac(t(x), 2)) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . t(x))

METHOD:

-/
theorem proof_gap_exercise_2245_4
  (t : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → 5 - 4 * x > 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → t x ∈ Set.Icc (1 : ℝ) 3)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → x = (5 - (t x)^2) / 4)
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) →
      differential (fun y : ℝ => y) =
        (fun y : Set.Icc (-1 : ℝ) 1 => (-(t y.val / 2)) • differential t y) := by
  sorry

/- Exercise 2245, gap 5
SHA-256: bd1fe9d67f437e2dc74b05aaaed6acd8582e7c26c740392820a90591e4f3da0a
PROOF GAP @5
ASSUM:
1. t : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ 5 - 4 * x > 0
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ t(x) ∈ [1, 3]
4. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ x = frac(5 - t(x)^{2}, 4)
5. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x) = (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . -frac(t(x), 2)) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . t(x))

GOAL:
DefInt(-1, 1, (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . frac(x, sqrtn(2, 5 - 4 * x))) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x)) = -DefInt(3, 1, (fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . frac(5 - t^{2}, 8)) * diff(fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . t))

METHOD:

-/
theorem proof_gap_exercise_2245_5
  (t : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → 5 - 4 * x > 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → t x ∈ Set.Icc (1 : ℝ) 3)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → x = (5 - (t x)^2) / 4)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) →
      differential (fun y : ℝ => y) =
        (fun y : Set.Icc (-1 : ℝ) 1 => (-(t y.val / 2)) • differential t y))
  : (∫ x in (-1 : ℝ)..(1 : ℝ), x / Real.sqrt (5 - 4 * x)) = (-(∫ u in (3 : ℝ)..(1 : ℝ), (5 - u^2) / 8)) := by
  sorry

/- Exercise 2245, gap 6
SHA-256: d184787eaa98c52c67c177b57da2bd4275538555c08e3d22ac2556dc8b940c6b
PROOF GAP @6
ASSUM:
1. t : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ 5 - 4 * x > 0
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ t(x) ∈ [1, 3]
4. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ x = frac(5 - t(x)^{2}, 4)
5. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x) = (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . -frac(t(x), 2)) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . t(x))
6. DefInt(-1, 1, (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . frac(x, sqrtn(2, 5 - 4 * x))) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x)) = -DefInt(3, 1, (fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . frac(5 - t^{2}, 8)) * diff(fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . t))

GOAL:
-DefInt(3, 1, (fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . frac(5 - t^{2}, 8)) * diff(fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . t)) = frac(1, 6)

METHOD:

-/
theorem proof_gap_exercise_2245_6
  (t : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → 5 - 4 * x > 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → t x ∈ Set.Icc (1 : ℝ) 3)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → x = (5 - (t x)^2) / 4)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) →
      differential (fun y : ℝ => y) =
        (fun y : Set.Icc (-1 : ℝ) 1 => (-(t y.val / 2)) • differential t y))
  (h5 : (∫ x in (-1 : ℝ)..(1 : ℝ), x / Real.sqrt (5 - 4 * x)) = (-(∫ u in (3 : ℝ)..(1 : ℝ), (5 - u^2) / 8)))
  : (-(∫ u in (3 : ℝ)..(1 : ℝ), (5 - u^2) / 8)) = (1 : ℝ) / 6 := by
  sorry

/- Exercise 2245, gap 7
SHA-256: b09348240981d5c5dc814cf8ddc44abbd4c3187de810279eeefa0e5868ceb7c5
PROOF GAP @7
ASSUM:
1. t : RealSet → RealSet
2. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ 5 - 4 * x > 0
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ t(x) ∈ [1, 3]
4. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ x = frac(5 - t(x)^{2}, 4)
5. forall (x), x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1) ∧ t(x) = sqrtn(2, 5 - 4 * x) ⇒ diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x) = (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . -frac(t(x), 2)) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . t(x))
6. DefInt(-1, 1, (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . frac(x, sqrtn(2, 5 - 4 * x))) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x)) = -DefInt(3, 1, (fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . frac(5 - t^{2}, 8)) * diff(fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . t))
7. -DefInt(3, 1, (fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . frac(5 - t^{2}, 8)) * diff(fun t [t ∈ RealSet ∧ t ∈ IntervalCC(1, 3)] . t)) = frac(1, 6)

GOAL:
DefInt(-1, 1, (fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . frac(x, sqrtn(2, 5 - 4 * x))) * diff(fun x [x ∈ RealSet ∧ x ∈ IntervalCC(-1, 1)] . x)) = frac(1, 6)

METHOD:

-/
theorem proof_gap_exercise_2245_7
  (t : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → 5 - 4 * x > 0)
  (h2 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → t x ∈ Set.Icc (1 : ℝ) 3)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) → x = (5 - (t x)^2) / 4)
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Icc (-1 : ℝ) 1 ∧ t x = Real.sqrt (5 - 4 * x) →
      differential (fun y : ℝ => y) =
        (fun y : Set.Icc (-1 : ℝ) 1 => (-(t y.val / 2)) • differential t y))
  (h5 : (∫ x in (-1 : ℝ)..(1 : ℝ), x / Real.sqrt (5 - 4 * x)) = (-(∫ u in (3 : ℝ)..(1 : ℝ), (5 - u^2) / 8)))
  (h6 : (-(∫ u in (3 : ℝ)..(1 : ℝ), (5 - u^2) / 8)) = (1 : ℝ) / 6)
  : (∫ x in (-1 : ℝ)..(1 : ℝ), x / Real.sqrt (5 - 4 * x)) = (1 : ℝ) / 6 := by
  sorry
