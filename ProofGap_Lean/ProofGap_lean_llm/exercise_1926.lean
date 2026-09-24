import Mathlib

set_option linter.style.longLine false

namespace Exercise1926

-- A restricted differential is a field of continuous linear maps on [0, ∞).
-- The source's outer t remains a scalar constant, not a new lambda binder.
noncomputable def differential (f : ℝ → ℝ) :
    {u : ℝ // 0 ≤ u} → (ℝ →L[ℝ] ℝ) :=
  fun u => fderivWithin ℝ f (Set.Ici 0) u.val

-- FunDeri(F, 1, 1) for a total real function is its first derivative.
-- Only explicitly restricted identity lambdas use derivWithin.
def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ u : ℝ, u ∈ (Set.univ : Set ℝ) ∧ 0 ≤ u →
    deriv F u = deriv (fun v : ℝ => v) u / (1 + Real.sqrt u)}

def scaledRationalPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ u : ℝ, u ∈ (Set.univ : Set ℝ) ∧ 0 ≤ u →
    deriv G u = (u / (1 + u)) * derivWithin (fun v : ℝ => v) (Set.Ici 0) u ∧
    F u = 2 * G u}

def scaledSplitPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ u : ℝ, u ∈ (Set.univ : Set ℝ) ∧ 0 ≤ u →
    deriv G u = (1 - 1 / (1 + u)) * derivWithin (fun v : ℝ => v) (Set.Ici 0) u ∧
    F u = 2 * G u}

def explicitTPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, K ∈ (Set.univ : Set ℝ) ∧
    ∀ u : ℝ, u ∈ (Set.univ : Set ℝ) ∧ 0 ≤ u →
      F u = 2 * (u - Real.log (1 + u)) + K}

def explicitXPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, K ∈ (Set.univ : Set ℝ) ∧
    ∀ u : ℝ, u ∈ (Set.univ : Set ℝ) ∧ 0 ≤ u →
      F u = 2 * Real.sqrt u - 2 * Real.log (1 + Real.sqrt u) + K}

end Exercise1926

open Exercise1926

/- Exercise 1926, gap 1
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)

GOAL:
t ≥ 0

METHOD:

-/
theorem proof_gap_exercise_1926_1
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  : t ≥ 0 := by
  sorry

/- Exercise 1926, gap 2
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)
5. t ≥ 0

GOAL:
x = t^{2}

METHOD:

-/
theorem proof_gap_exercise_1926_2
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  (h5 : t ≥ 0)
  : x = t ^ (2 : ℕ) := by
  sorry

/- Exercise 1926, gap 3
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)
5. t ≥ 0
6. x = t^{2}

GOAL:
diff(fun t [t ∈ RealSet ∧ t ≥ 0] . x) = 2 * t * diff(fun t [t ∈ RealSet ∧ t ≥ 0] . t)

METHOD:

-/
theorem proof_gap_exercise_1926_3
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  (h5 : t ≥ 0)
  (h6 : x = t ^ (2 : ℕ))
  : differential (fun _ : ℝ => x) = (2 * t) • differential (fun u : ℝ => u) := by
  sorry

/- Exercise 1926, gap 4
PROOF GAP @4
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)
5. t ≥ 0
6. x = t^{2}
7. diff(fun t [t ∈ RealSet ∧ t ≥ 0] . x) = 2 * t * diff(fun t [t ∈ RealSet ∧ t ≥ 0] . t)

GOAL:
{ `F_2` | forall (x), x ∈ RealSet ∧ x ≥ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), 1 + sqrtn(2, x)) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_3`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_4`(t) = 2 * `F_3`(t)) }

METHOD:

-/
theorem proof_gap_exercise_1926_4
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  (h5 : t ≥ 0)
  (h6 : x = t ^ (2 : ℕ))
  (h7 : differential (fun _ : ℝ => x) = (2 * t) • differential (fun u : ℝ => u))
  : originalPrimitives = scaledRationalPrimitives := by
  sorry

/- Exercise 1926, gap 5
PROOF GAP @5
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)
5. t ≥ 0
6. x = t^{2}
7. diff(fun t [t ∈ RealSet ∧ t ≥ 0] . x) = 2 * t * diff(fun t [t ∈ RealSet ∧ t ≥ 0] . t)
8. { `F_2` | forall (x), x ∈ RealSet ∧ x ≥ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), 1 + sqrtn(2, x)) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_3`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_4`(t) = 2 * `F_3`(t)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_5`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_6`(t) = 2 * `F_5`(t)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_7`, 1, 1)(t) = (1 - frac(1, 1 + t)) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_8`(t) = 2 * `F_7`(t)) }

METHOD:

-/
theorem proof_gap_exercise_1926_5
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  (h5 : t ≥ 0)
  (h6 : x = t ^ (2 : ℕ))
  (h7 : differential (fun _ : ℝ => x) = (2 * t) • differential (fun u : ℝ => u))
  (h8 : originalPrimitives = scaledRationalPrimitives)
  : scaledRationalPrimitives = scaledSplitPrimitives := by
  sorry

/- Exercise 1926, gap 6
PROOF GAP @6
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)
5. t ≥ 0
6. x = t^{2}
7. diff(fun t [t ∈ RealSet ∧ t ≥ 0] . x) = 2 * t * diff(fun t [t ∈ RealSet ∧ t ≥ 0] . t)
8. { `F_2` | forall (x), x ∈ RealSet ∧ x ≥ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), 1 + sqrtn(2, x)) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_3`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_4`(t) = 2 * `F_3`(t)) }
9. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_5`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_6`(t) = 2 * `F_5`(t)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_7`, 1, 1)(t) = (1 - frac(1, 1 + t)) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_8`(t) = 2 * `F_7`(t)) }

GOAL:
{ `F_10` | exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_9`, 1, 1)(t) = (1 - frac(1, 1 + t)) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_10`(t) = 2 * `F_9`(t)) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ `F_11`(t) = 2 * (t - ln(1 + t)) + C) }

METHOD:

-/
theorem proof_gap_exercise_1926_6
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  (h5 : t ≥ 0)
  (h6 : x = t ^ (2 : ℕ))
  (h7 : differential (fun _ : ℝ => x) = (2 * t) • differential (fun u : ℝ => u))
  (h8 : originalPrimitives = scaledRationalPrimitives)
  (h9 : scaledRationalPrimitives = scaledSplitPrimitives)
  : scaledSplitPrimitives = explicitTPrimitives := by
  sorry

/- Exercise 1926, gap 7
PROOF GAP @7
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)
5. t ≥ 0
6. x = t^{2}
7. diff(fun t [t ∈ RealSet ∧ t ≥ 0] . x) = 2 * t * diff(fun t [t ∈ RealSet ∧ t ≥ 0] . t)
8. { `F_2` | forall (x), x ∈ RealSet ∧ x ≥ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), 1 + sqrtn(2, x)) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_3`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_4`(t) = 2 * `F_3`(t)) }
9. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_5`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_6`(t) = 2 * `F_5`(t)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_7`, 1, 1)(t) = (1 - frac(1, 1 + t)) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_8`(t) = 2 * `F_7`(t)) }
10. { `F_10` | exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_9`, 1, 1)(t) = (1 - frac(1, 1 + t)) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_10`(t) = 2 * `F_9`(t)) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ `F_11`(t) = 2 * (t - ln(1 + t)) + C) }

GOAL:
2 * (t - ln(1 + t)) + C = 2 * sqrtn(2, x) - 2 * ln(1 + sqrtn(2, x)) + C

METHOD:

-/
theorem proof_gap_exercise_1926_7
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  (h5 : t ≥ 0)
  (h6 : x = t ^ (2 : ℕ))
  (h7 : differential (fun _ : ℝ => x) = (2 * t) • differential (fun u : ℝ => u))
  (h8 : originalPrimitives = scaledRationalPrimitives)
  (h9 : scaledRationalPrimitives = scaledSplitPrimitives)
  (h10 : scaledSplitPrimitives = explicitTPrimitives)
  : 2 * (t - Real.log (1 + t)) + C = 2 * Real.sqrt x - 2 * Real.log (1 + Real.sqrt x) + C := by
  sorry

/- Exercise 1926, gap 8
PROOF GAP @8
ASSUM:
1. x ∈ RealSet ∧ x ≥ 0
2. t ∈ RealSet ∧ t ≥ 0
3. C ∈ RealSet
4. t = sqrtn(2, x)
5. t ≥ 0
6. x = t^{2}
7. diff(fun t [t ∈ RealSet ∧ t ≥ 0] . x) = 2 * t * diff(fun t [t ∈ RealSet ∧ t ≥ 0] . t)
8. { `F_2` | forall (x), x ∈ RealSet ∧ x ≥ 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), 1 + sqrtn(2, x)) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_3`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_4`(t) = 2 * `F_3`(t)) }
9. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_5`, 1, 1)(t) = frac(t, 1 + t) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_6`(t) = 2 * `F_5`(t)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_7`, 1, 1)(t) = (1 - frac(1, 1 + t)) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_8`(t) = 2 * `F_7`(t)) }
10. { `F_10` | exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ FunDeri(`F_9`, 1, 1)(t) = (1 - frac(1, 1 + t)) * FunDeri(fun t [t ∈ RealSet ∧ t ≥ 0] . t, 1, 1)(t) ∧ `F_10`(t) = 2 * `F_9`(t)) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (t), t ∈ RealSet ∧ t ≥ 0 ⇒ `F_11`(t) = 2 * (t - ln(1 + t)) + C) }
11. 2 * (t - ln(1 + t)) + C = 2 * sqrtn(2, x) - 2 * ln(1 + sqrtn(2, x)) + C

GOAL:
{ `F_12` | forall (x), x ∈ RealSet ∧ x ≥ 0 ⇒ FunDeri(`F_12`, 1, 1)(x) = frac(FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x), 1 + sqrtn(2, x)) } = { `F_13` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ≥ 0 ⇒ `F_13`(x) = 2 * sqrtn(2, x) - 2 * ln(1 + sqrtn(2, x)) + C) }

METHOD:

-/
theorem proof_gap_exercise_1926_8
  (x t C : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ) ∧ x ≥ 0)
  (h2 : t ∈ (Set.univ : Set ℝ) ∧ t ≥ 0)
  (h3 : C ∈ (Set.univ : Set ℝ))
  (h4 : t = Real.sqrt x)
  (h5 : t ≥ 0)
  (h6 : x = t ^ (2 : ℕ))
  (h7 : differential (fun _ : ℝ => x) = (2 * t) • differential (fun u : ℝ => u))
  (h8 : originalPrimitives = scaledRationalPrimitives)
  (h9 : scaledRationalPrimitives = scaledSplitPrimitives)
  (h10 : scaledSplitPrimitives = explicitTPrimitives)
  (h11 : 2 * (t - Real.log (1 + t)) + C = 2 * Real.sqrt x - 2 * Real.log (1 + Real.sqrt x) + C)
  : originalPrimitives = explicitXPrimitives := by
  sorry

