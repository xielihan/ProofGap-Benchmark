import Mathlib

set_option linter.style.longLine false

namespace Exercise1932

-- Signed real cube root: the negative branch is essential for -1 < x < 1.
noncomputable def cubeRoot (y : ℝ) : ℝ :=
  if 0 ≤ y then Real.rpow y (1 / 3 : ℝ)
  else -Real.rpow (-y) (1 / 3 : ℝ)

def tDomain : Set ℝ := {u | u ∈ (Set.univ : Set ℝ) ∧ u ^ 3 ≠ 1}

-- Literal differential fields on the common domain. The x in the source
-- lambda is the outer scalar, not the inverse-substitution function.
-- The unrestricted identity differential is restricted only for comparison.
noncomputable def sourceDifferential (x t : ℝ) : Prop :=
  (fun u : tDomain => fderivWithin ℝ (fun _ : ℝ => x) tDomain (u : ℝ)) =
    (-(6 * t ^ 2) / (t ^ 3 - 1) ^ 2) •
      (fun u : tDomain => fderiv ℝ (fun v : ℝ => v) (u : ℝ))

noncomputable def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ u : ℝ, u ∈ (Set.univ : Set ℝ) ∧ u ≠ 1 ∧ u ≠ -1 →
    deriv F u = (1 / cubeRoot ((u + 1) ^ 2 * (u - 1) ^ 4)) *
      deriv (fun v : ℝ => v) u}

noncomputable def scaledPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ u : ℝ,
    u ∈ (Set.univ : Set ℝ) ∧ u ^ 3 ≠ 1 →
      deriv G u = deriv (fun v : ℝ => v) u ∧ F u = -(3 / 2 : ℝ) * G u}

def affinePrimitives : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, K ∈ (Set.univ : Set ℝ) ∧ ∀ u : ℝ,
    u ∈ (Set.univ : Set ℝ) ∧ u ^ 3 ≠ 1 → F u = -(3 / 2 : ℝ) * u + K}

noncomputable def answerPrimitives : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, K ∈ (Set.univ : Set ℝ) ∧ ∀ u : ℝ,
    u ∈ (Set.univ : Set ℝ) ∧ u ≠ 1 ∧ u ≠ -1 →
      F u = -(3 / 2 : ℝ) * cubeRoot ((u + 1) / (u - 1)) + K}

end Exercise1932

open Exercise1932

/- Exercise 1932, gap 1
SHA-256: 114ad2efb1f0725d9b5fd41f7fe54c7f4ec2169078e8e38e93857fef251dce98
PROOF GAP @1
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. x ≠ 1
4. x ≠ -1
5. t = sqrtn(3, frac(x + 1, x - 1))

GOAL:
t^{3} ≠ 1

METHOD:

-/
theorem proof_gap_exercise_1932_1
  (x C t : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : x ≠ 1)
  (h4 : x ≠ -1)
  (h5 : t = cubeRoot ((x + 1) / (x - 1)))
  : t ^ 3 ≠ 1 := by
  sorry

/- Exercise 1932, gap 2
SHA-256: 7c9a7da0d3f93536b6d23bacb96a7700abbe5b0d02c15dd92e81026b318fb0fe
PROOF GAP @2
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. x ≠ 1
4. x ≠ -1
5. t = sqrtn(3, frac(x + 1, x - 1))
6. t^{3} ≠ 1

GOAL:
x = frac(t^{3} + 1, t^{3} - 1)

METHOD:

-/
theorem proof_gap_exercise_1932_2
  (x C t : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : x ≠ 1)
  (h4 : x ≠ -1)
  (h5 : t = cubeRoot ((x + 1) / (x - 1)))
  (h6 : t ^ 3 ≠ 1)
  : x = (t ^ 3 + 1) / (t ^ 3 - 1) := by
  sorry

/- Exercise 1932, gap 3
SHA-256: fab7051e3f96bbd9eddc3196f9fe9fc25a646e11fefb806837f99ebdbae5b50a
PROOF GAP @3
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. x ≠ 1
4. x ≠ -1
5. t = sqrtn(3, frac(x + 1, x - 1))
6. t^{3} ≠ 1
7. x = frac(t^{3} + 1, t^{3} - 1)

GOAL:
diff(fun t [t ∈ RealSet ∧ t^{3} ≠ 1] . x) = -frac(6 * t^{2}, (t^{3} - 1)^{2}) * diff(fun t [t ∈ RealSet] . t)

METHOD:

-/
theorem proof_gap_exercise_1932_3
  (x C t : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : x ≠ 1)
  (h4 : x ≠ -1)
  (h5 : t = cubeRoot ((x + 1) / (x - 1)))
  (h6 : t ^ 3 ≠ 1)
  (h7 : x = (t ^ 3 + 1) / (t ^ 3 - 1))
  : sourceDifferential x t := by
  sorry

/- Exercise 1932, gap 4
SHA-256: 3d64f507bfbb352ad7b1d942a6de80fc8288f7af1a576f8c9f51b01467fa5f8e
PROOF GAP @4
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. x ≠ 1
4. x ≠ -1
5. t = sqrtn(3, frac(x + 1, x - 1))
6. t^{3} ≠ 1
7. x = frac(t^{3} + 1, t^{3} - 1)
8. diff(fun t [t ∈ RealSet ∧ t^{3} ≠ 1] . x) = -frac(6 * t^{2}, (t^{3} - 1)^{2}) * diff(fun t [t ∈ RealSet] . t)

GOAL:
{ `F_2` | forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -1 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(3, (x + 1)^{2} * (x - 1)^{4})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t^{3} ≠ 1 ⇒ FunDeri(`F_3`, 1, 1)(t) = FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ `F_4`(t) = -frac(3, 2) * `F_3`(t)) }

METHOD:

-/
theorem proof_gap_exercise_1932_4
  (x C t : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : x ≠ 1)
  (h4 : x ≠ -1)
  (h5 : t = cubeRoot ((x + 1) / (x - 1)))
  (h6 : t ^ 3 ≠ 1)
  (h7 : x = (t ^ 3 + 1) / (t ^ 3 - 1))
  (h8 : sourceDifferential x t)
  : originalPrimitives = scaledPrimitives := by
  sorry

/- Exercise 1932, gap 5
SHA-256: 0ba2030f5608b0c9c83370addb375cd49ba3f62756bad9c4a4fd29605d8287ce
PROOF GAP @5
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. x ≠ 1
4. x ≠ -1
5. t = sqrtn(3, frac(x + 1, x - 1))
6. t^{3} ≠ 1
7. x = frac(t^{3} + 1, t^{3} - 1)
8. diff(fun t [t ∈ RealSet ∧ t^{3} ≠ 1] . x) = -frac(6 * t^{2}, (t^{3} - 1)^{2}) * diff(fun t [t ∈ RealSet] . t)
9. { `F_2` | forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -1 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(3, (x + 1)^{2} * (x - 1)^{4})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t^{3} ≠ 1 ⇒ FunDeri(`F_3`, 1, 1)(t) = FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ `F_4`(t) = -frac(3, 2) * `F_3`(t)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t^{3} ≠ 1 ⇒ FunDeri(`F_5`, 1, 1)(t) = FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ `F_6`(t) = -frac(3, 2) * `F_5`(t)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (t), t ∈ RealSet ∧ t^{3} ≠ 1 ⇒ `F_7`(t) = -frac(3, 2) * t + C) }

METHOD:

-/
theorem proof_gap_exercise_1932_5
  (x C t : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : x ≠ 1)
  (h4 : x ≠ -1)
  (h5 : t = cubeRoot ((x + 1) / (x - 1)))
  (h6 : t ^ 3 ≠ 1)
  (h7 : x = (t ^ 3 + 1) / (t ^ 3 - 1))
  (h8 : sourceDifferential x t)
  (h9 : originalPrimitives = scaledPrimitives)
  : scaledPrimitives = affinePrimitives := by
  sorry

/- Exercise 1932, gap 6
SHA-256: 5181fadff8ff65257ba6f6943d88b9ba99ed4cc19203bdbb4f21fda34ad9eca8
PROOF GAP @6
ASSUM:
1. x ∈ RealSet
2. C ∈ RealSet
3. x ≠ 1
4. x ≠ -1
5. t = sqrtn(3, frac(x + 1, x - 1))
6. t^{3} ≠ 1
7. x = frac(t^{3} + 1, t^{3} - 1)
8. diff(fun t [t ∈ RealSet ∧ t^{3} ≠ 1] . x) = -frac(6 * t^{2}, (t^{3} - 1)^{2}) * diff(fun t [t ∈ RealSet] . t)
9. { `F_2` | forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -1 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(3, (x + 1)^{2} * (x - 1)^{4})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t^{3} ≠ 1 ⇒ FunDeri(`F_3`, 1, 1)(t) = FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ `F_4`(t) = -frac(3, 2) * `F_3`(t)) }
10. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ∧ t^{3} ≠ 1 ⇒ FunDeri(`F_5`, 1, 1)(t) = FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ `F_6`(t) = -frac(3, 2) * `F_5`(t)) } = { `F_7` | exists (C), C ∈ RealSet ∧ (forall (t), t ∈ RealSet ∧ t^{3} ≠ 1 ⇒ `F_7`(t) = -frac(3, 2) * t + C) }

GOAL:
{ `F_8` | forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -1 ⇒ FunDeri(`F_8`, 1, 1)(x) = frac(1, sqrtn(3, (x + 1)^{2} * (x - 1)^{4})) * FunDeri(fun x [x ∈ RealSet] . x, 1, 1)(x) } = { `F_9` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -1 ⇒ `F_9`(x) = -frac(3, 2) * sqrtn(3, frac(x + 1, x - 1)) + C) }

METHOD:

-/
theorem proof_gap_exercise_1932_6
  (x C t : ℝ)
  (h1 : x ∈ (Set.univ : Set ℝ))
  (h2 : C ∈ (Set.univ : Set ℝ))
  (h3 : x ≠ 1)
  (h4 : x ≠ -1)
  (h5 : t = cubeRoot ((x + 1) / (x - 1)))
  (h6 : t ^ 3 ≠ 1)
  (h7 : x = (t ^ 3 + 1) / (t ^ 3 - 1))
  (h8 : sourceDifferential x t)
  (h9 : originalPrimitives = scaledPrimitives)
  (h10 : scaledPrimitives = affinePrimitives)
  : originalPrimitives = answerPrimitives := by
  sorry

