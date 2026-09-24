import Mathlib

/- All sixteen source gaps are reproduced verbatim below.
Proof placeholders are intentional. See reviews/exercise_1576.json for source issues.
Coordinate occurrences of IntervalLoRo are resolved from the original and RNFL.
ContinuousFuncOn is relative continuity on the stated closed domain.
The final existential implication is preserved, not strengthened to a conjunction. -/

open scoped Pointwise
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

/-- The global maximizers on the given set (including membership). -/
def exercise1576MaximumPointsOn (f : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {x | x ∈ s ∧ ∀ y ∈ s, f y ≤ f x}

-- Exercise 1576, gap 1
/-
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}

GOAL:
ContinuousFuncOn(f, [-b, b])

METHOD:

-/
theorem proof_gap_exercise_1576_1
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  : ContinuousOn f (Set.Icc (-b) b) := by
  sorry

-- Exercise 1576, gap 2
/-
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])

GOAL:
DiffableFuncOn(f, IntervalLoRo(-b, b))

METHOD:

-/
theorem proof_gap_exercise_1576_2
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  : DifferentiableOn ℝ f (Set.Ioo (-b) b) := by
  sorry

-- Exercise 1576, gap 3
/-
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))

GOAL:
forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b

METHOD:

-/
theorem proof_gap_exercise_1576_3
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b := by
  sorry

-- Exercise 1576, gap 4
/-
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b

GOAL:
b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0

METHOD:

-/
theorem proof_gap_exercise_1576_4
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0 := by
  sorry

-- Exercise 1576, gap 5
/-
PROOF GAP @5
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0

GOAL:
b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]

METHOD:

-/
theorem proof_gap_exercise_1576_5
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b := by
  sorry

-- Exercise 1576, gap 6
/-
PROOF GAP @6
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]

GOAL:
b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))

METHOD:

-/
theorem proof_gap_exercise_1576_6
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4) := by
  sorry

-- Exercise 1576, gap 7
/-
PROOF GAP @7
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))

GOAL:
b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))

METHOD:

-/
theorem proof_gap_exercise_1576_7
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)) := by
  sorry

-- Exercise 1576, gap 8
/-
PROOF GAP @8
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))

GOAL:
b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)

METHOD:

-/
theorem proof_gap_exercise_1576_8
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c := by
  sorry

-- Exercise 1576, gap 9
/-
PROOF GAP @9
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)

GOAL:
b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))

METHOD:

-/
theorem proof_gap_exercise_1576_9
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c := by
  sorry

-- Exercise 1576, gap 10
/-
PROOF GAP @10
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)
16. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))

GOAL:
b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P ∈ { IntervalLoRo(frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})), IntervalLoRo(-frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})) })

METHOD:

-/
theorem proof_gap_exercise_1576_10
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  (h16 : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c)
  : b ≤ a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P ∈ ({(a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2), (-(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2)} : Set (ℝ × ℝ)) := by
  sorry

-- Exercise 1576, gap 11
/-
PROOF GAP @11
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)
16. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))
17. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P ∈ { IntervalLoRo(frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})), IntervalLoRo(-frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})) })

GOAL:
b > frac(a, sqrtn(2, 2)) ⇒ (forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) > 0)

METHOD:

-/
theorem proof_gap_exercise_1576_11
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  (h16 : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c)
  (h17 : b ≤ a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P ∈ ({(a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2), (-(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2)} : Set (ℝ × ℝ)))
  : b > a / Real.sqrt 2 → ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y > 0 := by
  sorry

-- Exercise 1576, gap 12
/-
PROOF GAP @12
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)
16. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))
17. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P ∈ { IntervalLoRo(frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})), IntervalLoRo(-frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})) })
18. b > frac(a, sqrtn(2, 2)) ⇒ (forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) > 0)

GOAL:
b > frac(a, sqrtn(2, 2)) ⇒ MaximumPointOn(f, [-b, b]) = { b }

METHOD:

-/
theorem proof_gap_exercise_1576_12
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  (h16 : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c)
  (h17 : b ≤ a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P ∈ ({(a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2), (-(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2)} : Set (ℝ × ℝ)))
  (h18 : b > a / Real.sqrt 2 → ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y > 0)
  : b > a / Real.sqrt 2 → exercise1576MaximumPointsOn f (Set.Icc (-b) b) = {b} := by
  sorry

-- Exercise 1576, gap 13
/-
PROOF GAP @13
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)
16. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))
17. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P ∈ { IntervalLoRo(frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})), IntervalLoRo(-frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})) })
18. b > frac(a, sqrtn(2, 2)) ⇒ (forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) > 0)
19. b > frac(a, sqrtn(2, 2)) ⇒ MaximumPointOn(f, [-b, b]) = { b }

GOAL:
b > frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(b)) = 2 * b

METHOD:

-/
theorem proof_gap_exercise_1576_13
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  (h16 : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c)
  (h17 : b ≤ a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P ∈ ({(a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2), (-(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2)} : Set (ℝ × ℝ)))
  (h18 : b > a / Real.sqrt 2 → ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y > 0)
  (h19 : b > a / Real.sqrt 2 → exercise1576MaximumPointsOn f (Set.Icc (-b) b) = {b})
  : b > a / Real.sqrt 2 → Real.sqrt (f b) = 2 * b := by
  sorry

-- Exercise 1576, gap 14
/-
PROOF GAP @14
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)
16. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))
17. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P ∈ { IntervalLoRo(frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})), IntervalLoRo(-frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})) })
18. b > frac(a, sqrtn(2, 2)) ⇒ (forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) > 0)
19. b > frac(a, sqrtn(2, 2)) ⇒ MaximumPointOn(f, [-b, b]) = { b }
20. b > frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(b)) = 2 * b

GOAL:
b > frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = 2 * b)

METHOD:

-/
theorem proof_gap_exercise_1576_14
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  (h16 : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c)
  (h17 : b ≤ a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P ∈ ({(a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2), (-(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2)} : Set (ℝ × ℝ)))
  (h18 : b > a / Real.sqrt 2 → ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y > 0)
  (h19 : b > a / Real.sqrt 2 → exercise1576MaximumPointsOn f (Set.Icc (-b) b) = {b})
  (h20 : b > a / Real.sqrt 2 → Real.sqrt (f b) = 2 * b)
  : b > a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = 2 * b := by
  sorry

-- Exercise 1576, gap 15
/-
PROOF GAP @15
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)
16. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))
17. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P ∈ { IntervalLoRo(frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})), IntervalLoRo(-frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})) })
18. b > frac(a, sqrtn(2, 2)) ⇒ (forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) > 0)
19. b > frac(a, sqrtn(2, 2)) ⇒ MaximumPointOn(f, [-b, b]) = { b }
20. b > frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(b)) = 2 * b
21. b > frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = 2 * b)

GOAL:
b > frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P = (0, b))

METHOD:

-/
theorem proof_gap_exercise_1576_15
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  (h16 : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c)
  (h17 : b ≤ a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P ∈ ({(a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2), (-(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2)} : Set (ℝ × ℝ)))
  (h18 : b > a / Real.sqrt 2 → ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y > 0)
  (h19 : b > a / Real.sqrt 2 → exercise1576MaximumPointsOn f (Set.Icc (-b) b) = {b})
  (h20 : b > a / Real.sqrt 2 → Real.sqrt (f b) = 2 * b)
  (h21 : b > a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = 2 * b)
  : b > a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P = (0, b) := by
  sorry

-- Exercise 1576, gap 16
/-
PROOF GAP @16
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet ∧ 0 < b
3. c ∈ RealSet
4. f : RealSet → RealSet
5. b < a
6. c = sqrtn(2, a^{2} - b^{2})
7. forall (y), y ∈ RealSet ∧ -b ≤ y ∧ y ≤ b ⇒ f(y) = (1 - frac(a^{2}, b^{2})) * y^{2} + 2 * b * y + a^{2} + b^{2}
8. ContinuousFuncOn(f, [-b, b])
9. DiffableFuncOn(f, IntervalLoRo(-b, b))
10. forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) = 2 * (1 - frac(a^{2}, b^{2})) * y + 2 * b
11. b ≤ frac(a, sqrtn(2, 2)) ⇒ FunDeri(f, 1, 1)(frac(b^{3}, c^{2})) = 0
12. b ≤ frac(a, sqrtn(2, 2)) ⇒ frac(b^{3}, c^{2}) ∈ [-b, b]
13. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ x^{2} = a^{2} * (1 - frac(b^{4}, c^{4})))
14. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (x), x ∈ RealSet ∧ (x = frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}) ∨ x = -frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2})))
15. b ≤ frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(frac(b^{3}, c^{2}))) = frac(a^{2}, c)
16. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = frac(a^{2}, c))
17. b ≤ frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P ∈ { IntervalLoRo(frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})), IntervalLoRo(-frac(a^{2}, c^{2}) * sqrtn(2, a^{2} - 2 * b^{2}), frac(b^{3}, c^{2})) })
18. b > frac(a, sqrtn(2, 2)) ⇒ (forall (y), y ∈ RealSet ∧ -b < y ∧ y < b ⇒ FunDeri(f, 1, 1)(y) > 0)
19. b > frac(a, sqrtn(2, 2)) ⇒ MaximumPointOn(f, [-b, b]) = { b }
20. b > frac(a, sqrtn(2, 2)) ⇒ sqrtn(2, f(b)) = 2 * b
21. b > frac(a, sqrtn(2, 2)) ⇒ (exists (L), L ∈ RealSet ∧ L = 2 * b)
22. b > frac(a, sqrtn(2, 2)) ⇒ (exists (P), P ∈ CartesianProd(RealSet, RealSet) ∧ P = (0, b))

GOAL:
exists (L), L ∈ RealSet ∧ (L = cases{ frac(a^{2}, c) if b ≤ frac(a, sqrtn(2, 2)); 2 * b if b > frac(a, sqrtn(2, 2)) } ⇒ L = max({ sqrtn(2, f(y)) | y ∈ [-b, b] }))

METHOD:

-/
theorem proof_gap_exercise_1576_16
  (a b c : ℝ) (f : ℝ → ℝ)
  (h1 : a ∈ (Set.univ : Set ℝ))
  (h2 : b ∈ (Set.univ : Set ℝ) ∧ 0 < b)
  (h3 : c ∈ (Set.univ : Set ℝ))
  (h5 : b < a)
  (h6 : c = Real.sqrt (a^2 - b^2))
  (h7 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b ≤ y ∧ y ≤ b → f y = (1 - a^2 / b^2) * y^2 + 2 * b * y + a^2 + b^2)
  (h8 : ContinuousOn f (Set.Icc (-b) b))
  (h9 : DifferentiableOn ℝ f (Set.Ioo (-b) b))
  (h10 : ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y = 2 * (1 - a^2 / b^2) * y + 2 * b)
  (h11 : b ≤ a / Real.sqrt 2 → deriv f (b^3 / c^2) = 0)
  (h12 : b ≤ a / Real.sqrt 2 → b^3 / c^2 ∈ Set.Icc (-b) b)
  (h13 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x^2 = a^2 * (1 - b^4 / c^4))
  (h14 : b ≤ a / Real.sqrt 2 → ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ (x = a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2) ∨ x = -(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2)))
  (h15 : b ≤ a / Real.sqrt 2 → Real.sqrt (f (b^3 / c^2)) = a^2 / c)
  (h16 : b ≤ a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = a^2 / c)
  (h17 : b ≤ a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P ∈ ({(a^2 / c^2 * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2), (-(a^2 / c^2) * Real.sqrt (a^2 - 2 * b^2), b^3 / c^2)} : Set (ℝ × ℝ)))
  (h18 : b > a / Real.sqrt 2 → ∀ y : ℝ, y ∈ (Set.univ : Set ℝ) ∧ -b < y ∧ y < b → deriv f y > 0)
  (h19 : b > a / Real.sqrt 2 → exercise1576MaximumPointsOn f (Set.Icc (-b) b) = {b})
  (h20 : b > a / Real.sqrt 2 → Real.sqrt (f b) = 2 * b)
  (h21 : b > a / Real.sqrt 2 → ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ L = 2 * b)
  (h22 : b > a / Real.sqrt 2 → ∃ P : ℝ × ℝ, P ∈ (Set.univ : Set ℝ) ×ˢ (Set.univ : Set ℝ) ∧ P = (0, b))
  : ∃ L : ℝ, L ∈ (Set.univ : Set ℝ) ∧ (L = (if b ≤ a / Real.sqrt 2 then a^2 / c else 2 * b) → L = sSup ((fun y : ℝ => Real.sqrt (f y)) '' Set.Icc (-b) b)) := by
  sorry

