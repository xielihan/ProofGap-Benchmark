import Mathlib

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

-- IntegerSet embedded in the real domain of f.
def exercise7314IntegerPoints : Set ℝ := {x | ∃ k : ℤ, (k : ℝ) = x}

-- Cotangent is cos / sin on its natural domain; Lean division totalizes at poles.
noncomputable def exercise7314CotSq (x : ℝ) : ℝ :=
  (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) ^ (2 : ℕ)

-- Infinite discontinuity: discontinuous, with an infinite magnitude limit
-- on at least one side. This includes either sign of infinity.
def exercise7314InfiniteSingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ¬ ContinuousAt f a ∧
    (Tendsto (fun x => |f x|) (𝓝[<] a) atTop ∨
     Tendsto (fun x => |f x|) (𝓝[>] a) atTop)

-- Exercise 731_4, gap 1
-- SHA-256: 6b4717fea33f308eef5f2575efdb89c6cc8400c4e17df1145e2a49de06289b20
/-
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ cot(π * x)^{2} if x ∉ IntegerSet; 0 if x ∈ IntegerSet }

GOAL:
forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (cot(π * x)^{2}) = ∞

METHOD:

-/
theorem proof_gap_exercise_731_4_1
  (f : ℝ → ℝ)
  (h_definition : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∉ exercise7314IntegerPoints then exercise7314CotSq x else 0)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto exercise7314CotSq (𝓝[≠] (k : ℝ)) atTop := by
  sorry

-- Exercise 731_4, gap 2
-- SHA-256: 86a519d81b18042a8e58dad604182b7605671573432d553db2a672b16039f86c
/-
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ cot(π * x)^{2} if x ∉ IntegerSet; 0 if x ∈ IntegerSet }
3. forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (cot(π * x)^{2}) = ∞

GOAL:
forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (f(x)) = ∞

METHOD:

-/
theorem proof_gap_exercise_731_4_2
  (f : ℝ → ℝ)
  (h_definition : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∉ exercise7314IntegerPoints then exercise7314CotSq x else 0)
  (h_cot_limit : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto exercise7314CotSq (𝓝[≠] (k : ℝ)) atTop)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto f (𝓝[≠] (k : ℝ)) atTop := by
  sorry

-- Exercise 731_4, gap 3
-- SHA-256: 9d4a6b10dcd0109b382753a2b325a152e0291b83d2e0d75228c0081ce20488f1
/-
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ cot(π * x)^{2} if x ∉ IntegerSet; 0 if x ∈ IntegerSet }
3. forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (cot(π * x)^{2}) = ∞
4. forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (f(x)) = ∞

GOAL:
forall (k), k ∈ IntegerSet ⇒ InfiniteSingularPoint(f, k)

METHOD:

-/
theorem proof_gap_exercise_731_4_3
  (f : ℝ → ℝ)
  (h_definition : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∉ exercise7314IntegerPoints then exercise7314CotSq x else 0)
  (h_cot_limit : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto exercise7314CotSq (𝓝[≠] (k : ℝ)) atTop)
  (h_f_limit : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto f (𝓝[≠] (k : ℝ)) atTop)
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    exercise7314InfiniteSingularPoint f (k : ℝ) := by
  sorry

-- Exercise 731_4, gap 4
-- SHA-256: 8e1fb9a459b70f63bfc4bdc66507e150000d4632ea9954e1e40b08e353fb84df
/-
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ cot(π * x)^{2} if x ∉ IntegerSet; 0 if x ∈ IntegerSet }
3. forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (cot(π * x)^{2}) = ∞
4. forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (f(x)) = ∞
5. forall (k), k ∈ IntegerSet ⇒ InfiniteSingularPoint(f, k)

GOAL:
forall (k), k ∈ IntegerSet ⇒ InfiniteSingularPoint(f, k)

METHOD:

-/
theorem proof_gap_exercise_731_4_4
  (f : ℝ → ℝ)
  (h_definition : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∉ exercise7314IntegerPoints then exercise7314CotSq x else 0)
  (h_cot_limit : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto exercise7314CotSq (𝓝[≠] (k : ℝ)) atTop)
  (h_f_limit : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto f (𝓝[≠] (k : ℝ)) atTop)
  (h_singular_1 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    exercise7314InfiniteSingularPoint f (k : ℝ))
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    exercise7314InfiniteSingularPoint f (k : ℝ) := by
  sorry

-- Exercise 731_4, gap 5
-- SHA-256: 4fc5e4adad651ffda4a1944c58c3872875deaf84a473e6a12ceb6c9e53787e62
/-
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ cot(π * x)^{2} if x ∉ IntegerSet; 0 if x ∈ IntegerSet }
3. forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (cot(π * x)^{2}) = ∞
4. forall (k), k ∈ IntegerSet ⇒ lim_{ x → k } (f(x)) = ∞
5. forall (k), k ∈ IntegerSet ⇒ InfiniteSingularPoint(f, k)
6. forall (k), k ∈ IntegerSet ⇒ InfiniteSingularPoint(f, k)

GOAL:
forall (k), k ∈ IntegerSet ⇒ InfiniteSingularPoint(f, k)

METHOD:

-/
theorem proof_gap_exercise_731_4_5
  (f : ℝ → ℝ)
  (h_definition : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
    f x = if x ∉ exercise7314IntegerPoints then exercise7314CotSq x else 0)
  (h_cot_limit : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto exercise7314CotSq (𝓝[≠] (k : ℝ)) atTop)
  (h_f_limit : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    Tendsto f (𝓝[≠] (k : ℝ)) atTop)
  (h_singular_1 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    exercise7314InfiniteSingularPoint f (k : ℝ))
  (h_singular_2 : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    exercise7314InfiniteSingularPoint f (k : ℝ))
  : ∀ k : ℤ, k ∈ (Set.univ : Set ℤ) →
    exercise7314InfiniteSingularPoint f (k : ℝ) := by
  sorry

