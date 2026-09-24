import Mathlib

open scoped Topology
open Filter

-- Bare ∞ is unsigned infinity, distinct from +∞ (the NFL grammar).
-- The source y : Real → Real is arbitrary at 1 and -2.
namespace Exercise689

-- Textbook definition: a discontinuity with at least one infinite one-sided limit.
-- Exercise 661, §7, paragraph before left continuity.
def InfiniteSingularPoint (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ ContinuousAt f c ∧
    (Tendsto (fun x : ℝ => |f x|) (𝓝[<] c) atTop ∨
     Tendsto (fun x : ℝ => |f x|) (𝓝[>] c) atTop)

end Exercise689

/- Exercise 689, gap 1
SHA-256: 0d14a38a332994596a123352c79166958f9a58e4e5ee6f9ccd32c0e7ebac8c8e
PROOF GAP @1
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)

GOAL:
forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)

METHOD:

-/
theorem proof_gap_exercise_689_1
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2) := by
  sorry

/- Exercise 689, gap 2
SHA-256: 7920680723c88ec7481f6507373a90165e719cd1ac8b436b5c06e68ae68f11ff
PROOF GAP @2
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)
4. forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)

GOAL:
forall (x), x ∈ RealSet ⇒ x^{2} - 1 = (x - 1) * (x + 1)

METHOD:

-/
theorem proof_gap_exercise_689_2
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x ^ 2 - 1 = (x - 1) * (x + 1) := by
  sorry

/- Exercise 689, gap 3
SHA-256: 281521189e704d9bd0b9c4236b0e1fd5ad9f606ce3f3e2b7e1fa2fc0b89b93c6
PROOF GAP @3
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)
4. forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)
5. forall (x), x ∈ RealSet ⇒ x^{2} - 1 = (x - 1) * (x + 1)

GOAL:
forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x + 1, (x - 1) * (x + 2))

METHOD:

-/
theorem proof_gap_exercise_689_3
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x ^ 2 - 1 = (x - 1) * (x + 1))
  : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x + 1) / ((x - 1) * (x + 2)) := by
  sorry

/- Exercise 689, gap 4
SHA-256: 3f6ebb66ce3e6abbcd3266f673019d6115a61a5ac8c18c60bc27a465f57d801e
PROOF GAP @4
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)
4. forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)
5. forall (x), x ∈ RealSet ⇒ x^{2} - 1 = (x - 1) * (x + 1)
6. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x + 1, (x - 1) * (x + 2))

GOAL:
lim_{ x → 1 } (y(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_689_4
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x ^ 2 - 1 = (x - 1) * (x + 1))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x + 1) / ((x - 1) * (x + 2)))
  : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (1 : ℝ)) atTop := by
  sorry

/- Exercise 689, gap 5
SHA-256: a4242f5cc7d6d2e0531eeb2f74c812d8362e8146ff1da9543e775bca1017d008
PROOF GAP @5
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)
4. forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)
5. forall (x), x ∈ RealSet ⇒ x^{2} - 1 = (x - 1) * (x + 1)
6. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x + 1, (x - 1) * (x + 2))
7. lim_{ x → 1 } (y(x)) = ∞

GOAL:
lim_{ x → -2 } (y(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_689_5
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x ^ 2 - 1 = (x - 1) * (x + 1))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x + 1) / ((x - 1) * (x + 2)))
  (h7 : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (1 : ℝ)) atTop)
  : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (-2 : ℝ)) atTop := by
  sorry

/- Exercise 689, gap 6
SHA-256: 5d7140a4522ed896e4232b2951ed842115a7c7a5f65227db4931e3b6e2044754
PROOF GAP @6
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)
4. forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)
5. forall (x), x ∈ RealSet ⇒ x^{2} - 1 = (x - 1) * (x + 1)
6. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x + 1, (x - 1) * (x + 2))
7. lim_{ x → 1 } (y(x)) = ∞
8. lim_{ x → -2 } (y(x)) = ∞

GOAL:
InfiniteSingularPoint(y, 1)

METHOD:

-/
theorem proof_gap_exercise_689_6
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x ^ 2 - 1 = (x - 1) * (x + 1))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x + 1) / ((x - 1) * (x + 2)))
  (h7 : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (1 : ℝ)) atTop)
  (h8 : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (-2 : ℝ)) atTop)
  : Exercise689.InfiniteSingularPoint y 1 := by
  sorry

/- Exercise 689, gap 7
SHA-256: 728ac8fb6442bb4d3d6062314fdacbe9b4e2bcbcb44418b06a9e78348794bb3e
PROOF GAP @7
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)
4. forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)
5. forall (x), x ∈ RealSet ⇒ x^{2} - 1 = (x - 1) * (x + 1)
6. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x + 1, (x - 1) * (x + 2))
7. lim_{ x → 1 } (y(x)) = ∞
8. lim_{ x → -2 } (y(x)) = ∞
9. InfiniteSingularPoint(y, 1)

GOAL:
InfiniteSingularPoint(y, -2)

METHOD:

-/
theorem proof_gap_exercise_689_7
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x ^ 2 - 1 = (x - 1) * (x + 1))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x + 1) / ((x - 1) * (x + 2)))
  (h7 : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (1 : ℝ)) atTop)
  (h8 : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (-2 : ℝ)) atTop)
  (h9 : Exercise689.InfiniteSingularPoint y 1)
  : Exercise689.InfiniteSingularPoint y (-2) := by
  sorry

/- Exercise 689, gap 8
SHA-256: 3dcb2713d5c76f98cca3a8f6575a0747079ad9f2c3e20816673feb3fa65975c7
PROOF GAP @8
ASSUM:
1. y : RealSet → RealSet
2. a ∈ RealSet
3. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x^{2} - 1, x^{3} - 3 * x + 2)
4. forall (x), x ∈ RealSet ⇒ x^{3} - 3 * x + 2 = (x - 1)^{2} * (x + 2)
5. forall (x), x ∈ RealSet ⇒ x^{2} - 1 = (x - 1) * (x + 1)
6. forall (x), x ∈ RealSet ∧ x ≠ 1 ∧ x ≠ -2 ⇒ y(x) = frac(x + 1, (x - 1) * (x + 2))
7. lim_{ x → 1 } (y(x)) = ∞
8. lim_{ x → -2 } (y(x)) = ∞
9. InfiniteSingularPoint(y, 1)
10. InfiniteSingularPoint(y, -2)

GOAL:
a ∈ { 1, -2 } ⇔ ¬ContinuousFuncAt(y, a)

METHOD:

-/
theorem proof_gap_exercise_689_8
  (y : ℝ → ℝ) (a : ℝ)
  (ha : a ∈ (Set.univ : Set ℝ))
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x ^ 2 - 1) / (x ^ 3 - 3 * x + 2))
  (h4 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2))
  (h5 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → x ^ 2 - 1 = (x - 1) * (x + 1))
  (h6 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ≠ 1 ∧ x ≠ -2 →
    y x = (x + 1) / ((x - 1) * (x + 2)))
  (h7 : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (1 : ℝ)) atTop)
  (h8 : Tendsto (fun x : ℝ => |y x|) (𝓝[≠] (-2 : ℝ)) atTop)
  (h9 : Exercise689.InfiniteSingularPoint y 1)
  (h10 : Exercise689.InfiniteSingularPoint y (-2))
  : a ∈ ({1, -2} : Set ℝ) ↔ ¬ ContinuousAt y a := by
  sorry

