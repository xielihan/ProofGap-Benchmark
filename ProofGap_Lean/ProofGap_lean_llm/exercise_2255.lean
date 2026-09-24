import Mathlib

set_option autoImplicit false
set_option linter.style.longLine false

namespace Exercise2255

-- The differential identity is interpreted on its explicitly stated closed domain.
-- HasDerivWithinAt records existence, including at the endpoints; using totalized
-- deriv alone would conceal the source error at zero. No endpoint is removed.
def SqrtDifferentialOn (a : ℝ) (x : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2),
    HasDerivWithinAt x (1 / (2 * Real.sqrt t)) (Set.Icc 0 (a ^ 2)) t

/- Exercise 2255, gap 1 (verbatim)
PROOF GAP @1
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)

GOAL:
forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0

METHOD:

-/
theorem proof_gap_exercise_2255_1
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  : ∀ t : ℝ, t = 0 → x t = 0 := by
  sorry

/- Exercise 2255, gap 2 (verbatim)
PROOF GAP @2
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)
5. forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0

GOAL:
forall (t), t ∈ RealSet ∧ t = a^{2} ⇒ x(t) = a

METHOD:

-/
theorem proof_gap_exercise_2255_2
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  (h5 : ∀ t : ℝ, t = 0 → x t = 0)
  : ∀ t : ℝ, t = a ^ 2 → x t = a := by
  sorry

/- Exercise 2255, gap 3 (verbatim)
PROOF GAP @3
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)
5. forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0
6. forall (t), t ∈ RealSet ∧ t = a^{2} ⇒ x(t) = a
7. a > 0 ∧ ContinuousFuncOn(f, [0, a^{2}])

GOAL:
diff(x) = (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(1, 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)

METHOD:

-/
theorem proof_gap_exercise_2255_3
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  (h5 : ∀ t : ℝ, t = 0 → x t = 0)
  (h6 : ∀ t : ℝ, t = a ^ 2 → x t = a)
  (h7 : 0 < a ∧ (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  : SqrtDifferentialOn a x := by
  sorry

/- Exercise 2255, gap 4 (verbatim)
PROOF GAP @4
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)
5. forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0
6. forall (t), t ∈ RealSet ∧ t = a^{2} ⇒ x(t) = a
7. diff(x) = (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(1, 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)
8. a > 0 ∧ ContinuousFuncOn(f, [0, a^{2}])

GOAL:
DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))

METHOD:
[@method 代入 x(t) = sqrtn(2, t) 到 DefInt(0, a, (fun x . x^{3} * f(x^{2})) * diff(fun x . x)) @]
-/
theorem proof_gap_exercise_2255_4
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  (h5 : ∀ t : ℝ, t = 0 → x t = 0)
  (h6 : ∀ t : ℝ, t = a ^ 2 → x t = a)
  (h7 : SqrtDifferentialOn a x)
  (h8 : 0 < a ∧ (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)) := by
  sorry

/- Exercise 2255, gap 5 (verbatim)
PROOF GAP @5
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)
5. forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0
6. forall (t), t ∈ RealSet ∧ t = a^{2} ⇒ x(t) = a
7. diff(x) = (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(1, 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)
8. DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))
9. a > 0 ∧ ContinuousFuncOn(f, [0, a^{2}])

GOAL:
DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)) = frac(1, 2) * DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t * f(t)) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))

METHOD:

-/
theorem proof_gap_exercise_2255_5
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  (h5 : ∀ t : ℝ, t = 0 → x t = 0)
  (h6 : ∀ t : ℝ, t = a ^ 2 → x t = a)
  (h7 : SqrtDifferentialOn a x)
  (h8 : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)))
  (h9 : 0 < a ∧ (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  : (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)) = ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(a ^ 2), t * f t) := by
  sorry

/- Exercise 2255, gap 6 (verbatim)
PROOF GAP @6
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)
5. forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0
6. forall (t), t ∈ RealSet ∧ t = a^{2} ⇒ x(t) = a
7. diff(x) = (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(1, 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)
8. DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))
9. DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)) = frac(1, 2) * DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t * f(t)) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))

GOAL:
frac(1, 2) * DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t * f(t)) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)) = frac(1, 2) * DefInt(0, a^{2}, (fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x * f(x)) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x))

METHOD:

-/
theorem proof_gap_exercise_2255_6
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  (h5 : ∀ t : ℝ, t = 0 → x t = 0)
  (h6 : ∀ t : ℝ, t = a ^ 2 → x t = a)
  (h7 : SqrtDifferentialOn a x)
  (h8 : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)))
  (h9 : (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)) = ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(a ^ 2), t * f t))
  : ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(a ^ 2), t * f t) = ((1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(a ^ 2), u * f u) := by
  sorry

/- Exercise 2255, gap 7 (verbatim)
PROOF GAP @7
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)
5. forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0
6. forall (t), t ∈ RealSet ∧ t = a^{2} ⇒ x(t) = a
7. diff(x) = (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(1, 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)
8. DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))
9. DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)) = frac(1, 2) * DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t * f(t)) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))
10. frac(1, 2) * DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t * f(t)) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)) = frac(1, 2) * DefInt(0, a^{2}, (fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x * f(x)) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x))
11. a > 0 ∧ ContinuousFuncOn(f, [0, a^{2}])

GOAL:
DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = frac(1, 2) * DefInt(0, a^{2}, (fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x * f(x)) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x))

METHOD:

-/
theorem proof_gap_exercise_2255_7
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  (h5 : ∀ t : ℝ, t = 0 → x t = 0)
  (h6 : ∀ t : ℝ, t = a ^ 2 → x t = a)
  (h7 : SqrtDifferentialOn a x)
  (h8 : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)))
  (h9 : (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)) = ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(a ^ 2), t * f t))
  (h10 : ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(a ^ 2), t * f t) = ((1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(a ^ 2), u * f u))
  (h11 : 0 < a ∧ (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = ((1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(a ^ 2), u * f u) := by
  sorry

/- Exercise 2255, gap 8 (verbatim)
PROOF GAP @8
ASSUM:
1. a ∈ RealSet ∧ a > 0
2. f : RealSet → RealSet ∧ ContinuousFuncOn(f, [0, a^{2}])
3. x : RealSet → RealSet
4. forall (t), t ∈ RealSet ∧ t ∈ [0, a^{2}] ⇒ x(t) = sqrtn(2, t)
5. forall (t), t ∈ RealSet ∧ t = 0 ⇒ x(t) = 0
6. forall (t), t ∈ RealSet ∧ t = a^{2} ⇒ x(t) = a
7. diff(x) = (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(1, 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)
8. DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))
9. DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . frac(t^{frac(3, 2)} * f(t), 2 * sqrtn(2, t))) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)) = frac(1, 2) * DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t * f(t)) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t))
10. frac(1, 2) * DefInt(0, a^{2}, (fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t * f(t)) * diff(fun t [t ∈ RealSet ∧ t ∈ [0, a^{2}]] . t)) = frac(1, 2) * DefInt(0, a^{2}, (fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x * f(x)) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x))
11. DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = frac(1, 2) * DefInt(0, a^{2}, (fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x * f(x)) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x))

GOAL:
DefInt(0, a, (fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x^{3} * f(x^{2})) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a]] . x)) = frac(1, 2) * DefInt(0, a^{2}, (fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x * f(x)) * diff(fun x [x ∈ RealSet ∧ x ∈ [0, a^{2}]] . x))

METHOD:

-/
theorem proof_gap_exercise_2255_8
  (a : ℝ) (f x : ℝ → ℝ)
  (h1 : 0 < a)
  (h2 : (∀ t ∈ Set.Icc (0 : ℝ) (a ^ 2), ContinuousAt f t))
  (h4 : ∀ t : ℝ, t ∈ Set.Icc 0 (a ^ 2) → x t = Real.sqrt t)
  (h5 : ∀ t : ℝ, t = 0 → x t = 0)
  (h6 : ∀ t : ℝ, t = a ^ 2 → x t = a)
  (h7 : SqrtDifferentialOn a x)
  (h8 : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)))
  (h9 : (∫ t in (0 : ℝ)..(a ^ 2), (Real.rpow t (3 / 2 : ℝ) * f t) / (2 * Real.sqrt t)) = ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(a ^ 2), t * f t))
  (h10 : ((1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(a ^ 2), t * f t) = ((1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(a ^ 2), u * f u))
  (h11 : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = ((1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(a ^ 2), u * f u))
  : (∫ u in (0 : ℝ)..a, u ^ 3 * f (u ^ 2)) = ((1 / 2 : ℝ) * ∫ u in (0 : ℝ)..(a ^ 2), u * f u) := by
  sorry

end Exercise2255
