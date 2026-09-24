import Mathlib

set_option linter.style.longLine false

namespace Exercise2129

-- All roots are evaluated at positive real arguments; rpow is the positive real root.
noncomputable def root (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (n : ℝ))

-- Equality of one-dimensional differentials on the stated open domain,
-- represented by equality of their coefficients of dx. The redundant outer
-- positive-x quantifier in the source is retained in each theorem.
def differentialIdentity (t : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → deriv (fun z : ℝ => z) y = 6 * t y ^ 5 * deriv t y

-- FunDeri(F,1,1)(x)=v means the first derivative exists and equals v.
-- The domain is open, so HasDerivAt at positive x models the restricted derivative.
def originalPrimitives : Set (ℝ → ℝ) :=
  {F | ∀ y : ℝ, 0 < y →
    HasDerivAt F ((1 / (root 2 y + root 3 y)) * deriv (fun z : ℝ => z) y) y}

def scaledRationalPrimitives (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ y : ℝ, 0 < y →
    HasDerivAt G ((t y ^ 3 / (t y + 1)) * deriv t y) y ∧ F y = 6 * G y}

def scaledExpandedPrimitives (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ, ∀ y : ℝ, 0 < y →
    HasDerivAt G ((t y ^ 2 - t y + 1 - 1 / (t y + 1)) * deriv t y) y ∧
    F y = 6 * G y}

def substitutedFamily (t : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ c : ℝ, ∀ y : ℝ, 0 < y →
    F y = 2 * t y ^ 3 - 3 * t y ^ 2 + 6 * t y - 6 * Real.log (1 + t y) + c}

def finalFamily : Set (ℝ → ℝ) :=
  {F | ∃ c : ℝ, ∀ y : ℝ, 0 < y →
    F y = 2 * root 2 y - 3 * root 3 y + 6 * root 6 y -
      6 * Real.log (1 + root 6 y) + c}

end Exercise2129

open Exercise2129

/- Exercise 2129, gap 1
SHA-256: 02652984deea71ace92a655dc2b37913463ced48e58b3cc8db70a5a8625290e8
PROOF GAP @1
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x > 0 ⇒ t(x) = sqrtn(6, x)

GOAL:
forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(2, x) = t(x)^{3}

METHOD:

-/
theorem proof_gap_exercise_2129_1
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : 0 < x)
  (h4 : ∀ y : ℝ, 0 < y → t y = root 6 y)
  : ∀ y : ℝ, 0 < y → root 2 y = t y ^ 3 := by
  sorry

/- Exercise 2129, gap 2
SHA-256: 3d299e735555aea977295826c3b17982e9961ce1dc0034d191e31ad17fe08ceb
PROOF GAP @2
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x > 0 ⇒ t(x) = sqrtn(6, x)
5. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(2, x) = t(x)^{3}

GOAL:
forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(3, x) = t(x)^{2}

METHOD:

-/
theorem proof_gap_exercise_2129_2
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : 0 < x)
  (h4 : ∀ y : ℝ, 0 < y → t y = root 6 y)
  (h5 : ∀ y : ℝ, 0 < y → root 2 y = t y ^ 3)
  : ∀ y : ℝ, 0 < y → root 3 y = t y ^ 2 := by
  sorry

/- Exercise 2129, gap 3
SHA-256: aa0181af9fa674d65ca54da4d94fa17d536f0e4785137b8c6ed34394b9fe5197
PROOF GAP @3
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x > 0 ⇒ t(x) = sqrtn(6, x)
5. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(2, x) = t(x)^{3}
6. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(3, x) = t(x)^{2}

GOAL:
forall (x), x ∈ RealSet ∧ x > 0 ⇒ diff(fun x [x ∈ RealSet ∧ x > 0] . x) = (fun x [x ∈ RealSet ∧ x > 0] . 6 * t(x)^{5}) * diff(fun x [x ∈ RealSet ∧ x > 0] . t(x))

METHOD:

-/
theorem proof_gap_exercise_2129_3
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : 0 < x)
  (h4 : ∀ y : ℝ, 0 < y → t y = root 6 y)
  (h5 : ∀ y : ℝ, 0 < y → root 2 y = t y ^ 3)
  (h6 : ∀ y : ℝ, 0 < y → root 3 y = t y ^ 2)
  : ∀ y : ℝ, 0 < y → differentialIdentity t := by
  sorry

/- Exercise 2129, gap 4
SHA-256: 567ff2b6124607d82e420b49df11b74f766b6e759b92070c7a2a166bb5efd82a
PROOF GAP @4
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x > 0 ⇒ t(x) = sqrtn(6, x)
5. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(2, x) = t(x)^{3}
6. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(3, x) = t(x)^{2}
7. forall (x), x ∈ RealSet ∧ x > 0 ⇒ diff(fun x [x ∈ RealSet ∧ x > 0] . x) = (fun x [x ∈ RealSet ∧ x > 0] . 6 * t(x)^{5}) * diff(fun x [x ∈ RealSet ∧ x > 0] . t(x))

GOAL:
{ `F_2` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(2, x) + sqrtn(3, x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x)^{3}, t(x) + 1) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_4`(x) = 6 * `F_3`(x)) }

METHOD:

-/
theorem proof_gap_exercise_2129_4
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : 0 < x)
  (h4 : ∀ y : ℝ, 0 < y → t y = root 6 y)
  (h5 : ∀ y : ℝ, 0 < y → root 2 y = t y ^ 3)
  (h6 : ∀ y : ℝ, 0 < y → root 3 y = t y ^ 2)
  (h7 : ∀ y : ℝ, 0 < y → differentialIdentity t)
  : originalPrimitives = scaledRationalPrimitives t := by
  sorry

/- Exercise 2129, gap 5
SHA-256: 0661ce0f14f7d82a9753d9d7df4743fadc5f5a6a4187096d081b51fa1e937717
PROOF GAP @5
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x > 0 ⇒ t(x) = sqrtn(6, x)
5. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(2, x) = t(x)^{3}
6. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(3, x) = t(x)^{2}
7. forall (x), x ∈ RealSet ∧ x > 0 ⇒ diff(fun x [x ∈ RealSet ∧ x > 0] . x) = (fun x [x ∈ RealSet ∧ x > 0] . 6 * t(x)^{5}) * diff(fun x [x ∈ RealSet ∧ x > 0] . t(x))
8. { `F_2` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(2, x) + sqrtn(3, x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x)^{3}, t(x) + 1) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_4`(x) = 6 * `F_3`(x)) }

GOAL:
{ `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_5`, 1, 1)(x) = frac(t(x)^{3}, t(x) + 1) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_6`(x) = 6 * `F_5`(x)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_7`, 1, 1)(x) = (t(x)^{2} - t(x) + 1 - frac(1, t(x) + 1)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_8`(x) = 6 * `F_7`(x)) }

METHOD:

-/
theorem proof_gap_exercise_2129_5
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : 0 < x)
  (h4 : ∀ y : ℝ, 0 < y → t y = root 6 y)
  (h5 : ∀ y : ℝ, 0 < y → root 2 y = t y ^ 3)
  (h6 : ∀ y : ℝ, 0 < y → root 3 y = t y ^ 2)
  (h7 : ∀ y : ℝ, 0 < y → differentialIdentity t)
  (h8 : originalPrimitives = scaledRationalPrimitives t)
  : scaledRationalPrimitives t = scaledExpandedPrimitives t := by
  sorry

/- Exercise 2129, gap 6
SHA-256: cd5edd092678c6891d66a4a70021e266cb3bdde115e9f062f20147057df770e3
PROOF GAP @6
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x > 0 ⇒ t(x) = sqrtn(6, x)
5. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(2, x) = t(x)^{3}
6. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(3, x) = t(x)^{2}
7. forall (x), x ∈ RealSet ∧ x > 0 ⇒ diff(fun x [x ∈ RealSet ∧ x > 0] . x) = (fun x [x ∈ RealSet ∧ x > 0] . 6 * t(x)^{5}) * diff(fun x [x ∈ RealSet ∧ x > 0] . t(x))
8. { `F_2` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(2, x) + sqrtn(3, x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x)^{3}, t(x) + 1) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_4`(x) = 6 * `F_3`(x)) }
9. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_5`, 1, 1)(x) = frac(t(x)^{3}, t(x) + 1) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_6`(x) = 6 * `F_5`(x)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_7`, 1, 1)(x) = (t(x)^{2} - t(x) + 1 - frac(1, t(x) + 1)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_8`(x) = 6 * `F_7`(x)) }

GOAL:
{ `F_10` | exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_9`, 1, 1)(x) = (t(x)^{2} - t(x) + 1 - frac(1, t(x) + 1)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_10`(x) = 6 * `F_9`(x)) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ `F_11`(x) = 2 * t(x)^{3} - 3 * t(x)^{2} + 6 * t(x) - 6 * ln(1 + t(x)) + C) }

METHOD:

-/
theorem proof_gap_exercise_2129_6
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : 0 < x)
  (h4 : ∀ y : ℝ, 0 < y → t y = root 6 y)
  (h5 : ∀ y : ℝ, 0 < y → root 2 y = t y ^ 3)
  (h6 : ∀ y : ℝ, 0 < y → root 3 y = t y ^ 2)
  (h7 : ∀ y : ℝ, 0 < y → differentialIdentity t)
  (h8 : originalPrimitives = scaledRationalPrimitives t)
  (h9 : scaledRationalPrimitives t = scaledExpandedPrimitives t)
  : scaledExpandedPrimitives t = substitutedFamily t := by
  sorry

/- Exercise 2129, gap 7
SHA-256: 5824a3da516140ec39b2d69753e915a972bf29db26086319742d581adf8a0ea2
PROOF GAP @7
ASSUM:
1. x ∈ RealSet ∧ x > 0
2. C ∈ RealSet
3. t : RealSet → RealSet
4. forall (x), x ∈ RealSet ∧ x > 0 ⇒ t(x) = sqrtn(6, x)
5. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(2, x) = t(x)^{3}
6. forall (x), x ∈ RealSet ∧ x > 0 ⇒ sqrtn(3, x) = t(x)^{2}
7. forall (x), x ∈ RealSet ∧ x > 0 ⇒ diff(fun x [x ∈ RealSet ∧ x > 0] . x) = (fun x [x ∈ RealSet ∧ x > 0] . 6 * t(x)^{5}) * diff(fun x [x ∈ RealSet ∧ x > 0] . t(x))
8. { `F_2` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_2`, 1, 1)(x) = frac(1, sqrtn(2, x) + sqrtn(3, x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_4` | exists (`F_3`), `F_3` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_3`, 1, 1)(x) = frac(t(x)^{3}, t(x) + 1) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_4`(x) = 6 * `F_3`(x)) }
9. { `F_6` | exists (`F_5`), `F_5` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_5`, 1, 1)(x) = frac(t(x)^{3}, t(x) + 1) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_6`(x) = 6 * `F_5`(x)) } = { `F_8` | exists (`F_7`), `F_7` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_7`, 1, 1)(x) = (t(x)^{2} - t(x) + 1 - frac(1, t(x) + 1)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_8`(x) = 6 * `F_7`(x)) }
10. { `F_10` | exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_9`, 1, 1)(x) = (t(x)^{2} - t(x) + 1 - frac(1, t(x) + 1)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . t(x), 1, 1)(x) ∧ `F_10`(x) = 6 * `F_9`(x)) } = { `F_11` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ `F_11`(x) = 2 * t(x)^{3} - 3 * t(x)^{2} + 6 * t(x) - 6 * ln(1 + t(x)) + C) }

GOAL:
{ `F_12` | forall (x), x ∈ RealSet ∧ x > 0 ⇒ FunDeri(`F_12`, 1, 1)(x) = frac(1, sqrtn(2, x) + sqrtn(3, x)) * FunDeri(fun x [x ∈ RealSet ∧ x > 0] . x, 1, 1)(x) } = { `F_13` | exists (C), C ∈ RealSet ∧ (forall (x), x ∈ RealSet ∧ x > 0 ⇒ `F_13`(x) = 2 * sqrtn(2, x) - 3 * sqrtn(3, x) + 6 * sqrtn(6, x) - 6 * ln(1 + sqrtn(6, x)) + C) }

METHOD:

-/
theorem proof_gap_exercise_2129_7
  (x C : ℝ) (t : ℝ → ℝ)
  (h1 : 0 < x)
  (h4 : ∀ y : ℝ, 0 < y → t y = root 6 y)
  (h5 : ∀ y : ℝ, 0 < y → root 2 y = t y ^ 3)
  (h6 : ∀ y : ℝ, 0 < y → root 3 y = t y ^ 2)
  (h7 : ∀ y : ℝ, 0 < y → differentialIdentity t)
  (h8 : originalPrimitives = scaledRationalPrimitives t)
  (h9 : scaledRationalPrimitives t = scaledExpandedPrimitives t)
  (h10 : scaledExpandedPrimitives t = substitutedFamily t)
  : originalPrimitives = finalFamily := by
  sorry

