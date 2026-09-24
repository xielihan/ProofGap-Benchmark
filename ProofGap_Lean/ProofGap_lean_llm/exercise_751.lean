import Mathlib

open Filter
open scoped Topology

namespace Exercise751

-- Definition 255: boundedness means a real upper bound for absolute values.
def BoundedOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ B : ℝ, ∀ t ∈ S, |f t| ≤ B

end Exercise751

-- RealSet is represented by ℝ and Set.univ. Defined is explicit value existence.
-- The original half-line domain uses relative continuity, including at a.
-- Both orientations of equality with an existing finite limit mean Tendsto.
-- In gaps 7–9, free M₁ is NOT identified with the existential witness.

/- Exercise 751, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))

GOAL:
A ∈ RealSet

METHOD:

-/
theorem proof_gap_exercise_751_1
  (f : ℝ → ℝ) (a x A : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  : A ∈ (Set.univ : Set ℝ) := by
  sorry

/- Exercise 751, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))

METHOD:

-/
theorem proof_gap_exercise_751_2
  (f : ℝ → ℝ) (a x A : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)) := by
  sorry

/- Exercise 751, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))

GOAL:
exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x)| < |A| + 1)

METHOD:

-/
theorem proof_gap_exercise_751_3
  (f : ℝ → ℝ) (a x A : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)))
  : ∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t| < |A| + 1) := by
  sorry

/- Exercise 751, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))
10. exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x)| < |A| + 1)

GOAL:
forall (X), X ∈ RealSet ∧ X > a ⇒ ContinuousFuncOn(f, [a, X])

METHOD:

-/
theorem proof_gap_exercise_751_4
  (f : ℝ → ℝ) (a x A : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)))
  (h10 : ∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t| < |A| + 1))
  : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → ContinuousOn f (Set.Icc a X) := by
  sorry

/- Exercise 751, gap 5
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))
10. exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x)| < |A| + 1)
11. forall (X), X ∈ RealSet ∧ X > a ⇒ ContinuousFuncOn(f, [a, X])

GOAL:
forall (X), X ∈ RealSet ∧ X > a ⇒ BoundedFuncOn(f, [a, X])

METHOD:

-/
theorem proof_gap_exercise_751_5
  (f : ℝ → ℝ) (a x A : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)))
  (h10 : ∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t| < |A| + 1))
  (h11 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → ContinuousOn f (Set.Icc a X))
  : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → Exercise751.BoundedOn f (Set.Icc a X) := by
  sorry

/- Exercise 751, gap 6
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))
10. exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x)| < |A| + 1)
11. forall (X), X ∈ RealSet ∧ X > a ⇒ ContinuousFuncOn(f, [a, X])
12. forall (X), X ∈ RealSet ∧ X > a ⇒ BoundedFuncOn(f, [a, X])

GOAL:
exists (M_{1}), M_{1} ∈ RealSet ∧ M_{1} > 0 ∧ (forall (x) (X), x ∈ RealSet ∧ X ∈ RealSet ∧ X > a ∧ x ∈ [a, X] ⇒ |f(x)| < M_{1})

METHOD:

-/
theorem proof_gap_exercise_751_6
  (f : ℝ → ℝ) (a x A : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)))
  (h10 : ∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t| < |A| + 1))
  (h11 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → ContinuousOn f (Set.Icc a X))
  (h12 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → Exercise751.BoundedOn f (Set.Icc a X))
  : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ B > 0 ∧ (∀ t X : ℝ, t ∈ (Set.univ : Set ℝ) ∧ X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ t ∈ Set.Icc a X → |f t| < B) := by
  sorry

/- Exercise 751, gap 7
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))
10. exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x)| < |A| + 1)
11. forall (X), X ∈ RealSet ∧ X > a ⇒ ContinuousFuncOn(f, [a, X])
12. forall (X), X ∈ RealSet ∧ X > a ⇒ BoundedFuncOn(f, [a, X])
13. exists (M_{1}), M_{1} ∈ RealSet ∧ M_{1} > 0 ∧ (forall (x) (X), x ∈ RealSet ∧ X ∈ RealSet ∧ X > a ∧ x ∈ [a, X] ⇒ |f(x)| < M_{1})
14. M = max(|A| + 1, M_{1})

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [a, +∞) ⇒ |f(x)| < M

METHOD:

-/
theorem proof_gap_exercise_751_7
  (f : ℝ → ℝ) (a x A : ℝ)
  (M M₁ : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)))
  (h10 : ∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t| < |A| + 1))
  (h11 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → ContinuousOn f (Set.Icc a X))
  (h12 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → Exercise751.BoundedOn f (Set.Icc a X))
  (h13 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ B > 0 ∧ (∀ t X : ℝ, t ∈ (Set.univ : Set ℝ) ∧ X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ t ∈ Set.Icc a X → |f t| < B))
  (h14 : M = max (|A| + 1) M₁)
  : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ici a → |f t| < M := by
  sorry

/- Exercise 751, gap 8
PROOF GAP @8
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))
10. exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x)| < |A| + 1)
11. forall (X), X ∈ RealSet ∧ X > a ⇒ ContinuousFuncOn(f, [a, X])
12. forall (X), X ∈ RealSet ∧ X > a ⇒ BoundedFuncOn(f, [a, X])
13. exists (M_{1}), M_{1} ∈ RealSet ∧ M_{1} > 0 ∧ (forall (x) (X), x ∈ RealSet ∧ X ∈ RealSet ∧ X > a ∧ x ∈ [a, X] ⇒ |f(x)| < M_{1})
14. M = max(|A| + 1, M_{1})
15. forall (x), x ∈ RealSet ∧ x ∈ [a, +∞) ⇒ |f(x)| < M

GOAL:
BoundedFuncOn(f, [a, +∞))

METHOD:

-/
theorem proof_gap_exercise_751_8
  (f : ℝ → ℝ) (a x A : ℝ)
  (M M₁ : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)))
  (h10 : ∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t| < |A| + 1))
  (h11 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → ContinuousOn f (Set.Icc a X))
  (h12 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → Exercise751.BoundedOn f (Set.Icc a X))
  (h13 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ B > 0 ∧ (∀ t X : ℝ, t ∈ (Set.univ : Set ℝ) ∧ X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ t ∈ Set.Icc a X → |f t| < B))
  (h14 : M = max (|A| + 1) M₁)
  (h15 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ici a → |f t| < M)
  : Exercise751.BoundedOn f (Set.Ici a) := by
  sorry

/- Exercise 751, gap 9
PROOF GAP @9
ASSUM:
1. f : RealSet → RealSet
2. a ∈ RealSet
3. x ∈ RealSet
4. Defined(f, [a, +∞))
5. ContinuousFuncOn(f, [a, +∞))
6. exists (A), A ∈ RealSet ∧ lim_{ x → +∞ } (f(x)) = A
7. A = lim_{ x → +∞ } (f(x))
8. A ∈ RealSet
9. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ ε = 1 ⇒ (exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x) - A| < 1))
10. exists (X), X ∈ RealSet ∧ X > a ∧ (forall (x), x ∈ RealSet ∧ x > X ⇒ |f(x)| < |A| + 1)
11. forall (X), X ∈ RealSet ∧ X > a ⇒ ContinuousFuncOn(f, [a, X])
12. forall (X), X ∈ RealSet ∧ X > a ⇒ BoundedFuncOn(f, [a, X])
13. exists (M_{1}), M_{1} ∈ RealSet ∧ M_{1} > 0 ∧ (forall (x) (X), x ∈ RealSet ∧ X ∈ RealSet ∧ X > a ∧ x ∈ [a, X] ⇒ |f(x)| < M_{1})
14. M = max(|A| + 1, M_{1})
15. forall (x), x ∈ RealSet ∧ x ∈ [a, +∞) ⇒ |f(x)| < M
16. BoundedFuncOn(f, [a, +∞))

GOAL:
BoundedFuncOn(f, [a, +∞))

METHOD:

-/
theorem proof_gap_exercise_751_9
  (f : ℝ → ℝ) (a x A : ℝ)
  (M M₁ : ℝ)
  (h2 : a ∈ (Set.univ : Set ℝ))
  (h3 : x ∈ (Set.univ : Set ℝ))
  (h4 : ∀ t ∈ Set.Ici a, ∃ y : ℝ, f t = y)
  (h5 : ContinuousOn f (Set.Ici a))
  (h6 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ Tendsto f atTop (𝓝 B))
  (h7 : Tendsto f atTop (𝓝 A))
  (h8 : A ∈ (Set.univ : Set ℝ))
  (h9 : ∀ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧ ε = 1 → (∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t - A| < 1)))
  (h10 : ∃ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ (∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t > X → |f t| < |A| + 1))
  (h11 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → ContinuousOn f (Set.Icc a X))
  (h12 : ∀ X : ℝ, X ∈ (Set.univ : Set ℝ) ∧ X > a → Exercise751.BoundedOn f (Set.Icc a X))
  (h13 : ∃ B : ℝ, B ∈ (Set.univ : Set ℝ) ∧ B > 0 ∧ (∀ t X : ℝ, t ∈ (Set.univ : Set ℝ) ∧ X ∈ (Set.univ : Set ℝ) ∧ X > a ∧ t ∈ Set.Icc a X → |f t| < B))
  (h14 : M = max (|A| + 1) M₁)
  (h15 : ∀ t : ℝ, t ∈ (Set.univ : Set ℝ) ∧ t ∈ Set.Ici a → |f t| < M)
  (h16 : Exercise751.BoundedOn f (Set.Ici a))
  : Exercise751.BoundedOn f (Set.Ici a) := by
  sorry

