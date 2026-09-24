import Mathlib

open Filter
open scoped Topology

-- The source gaps use x on |x| ≤ 1 and 1 otherwise, unlike the exercise statement.
-- Preserve the source gaps; see the semantic review for the input discrepancy.
namespace Exercise731_3

-- For a total real function, unequal finite one-sided limits define a jump.
-- The discontinuity clause is explicit; closure of the domain is all of ℝ.
def JumpSingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ¬ ContinuousAt f a ∧
    ∃ l r : ℝ, Tendsto f (𝓝[<] a) (𝓝 l) ∧
      Tendsto f (𝓝[>] a) (𝓝 r) ∧ l ≠ r

end Exercise731_3

/- Exercise 731_3, gap 1
SHA-256: 2f2755a710bda748c6200d7e8c60ace3dc30e5487bfb9bf69528245449469a4e
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }

GOAL:
lim_{ x → (-1)^- } (f(x)) = 1

METHOD:

-/
theorem proof_gap_exercise_731_3_1
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)) := by
  sorry

/- Exercise 731_3, gap 2
SHA-256: 4689a2e4cf7332bba5720922d362c6b238c4fbc6408289f39d3f435d6c3464f0
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1

GOAL:
lim_{ x → (-1)^+ } (f(x)) = -1

METHOD:

-/
theorem proof_gap_exercise_731_3_2
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)) := by
  sorry

/- Exercise 731_3, gap 3
SHA-256: e45c7a96a1943cbc684f48a789c60b0b481f070447423c9abeaf4918075eee77
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1
4. lim_{ x → (-1)^+ } (f(x)) = -1

GOAL:
¬ContinuousFuncAt(f, -1)

METHOD:

-/
theorem proof_gap_exercise_731_3_3
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  (h3 : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)))
  : ¬ ContinuousAt f (-1 : ℝ) := by
  sorry

/- Exercise 731_3, gap 4
SHA-256: 64a91d46b6a3c438a1457b2fef1fec5cb60bbdc20a903129ddd5bcc117a5e6cb
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1
4. lim_{ x → (-1)^+ } (f(x)) = -1
5. ¬ContinuousFuncAt(f, -1)

GOAL:
JumpSingularPoint(f, -1)

METHOD:

-/
theorem proof_gap_exercise_731_3_4
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  (h3 : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)))
  (h4 : ¬ ContinuousAt f (-1 : ℝ))
  : Exercise731_3.JumpSingularPoint f (-1 : ℝ) := by
  sorry

/- Exercise 731_3, gap 5
SHA-256: 7481a9e197dce98bb949b6e79b5071addc2b29de8683fcd9d0e6a527020b4303
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. forall (x), x ∈ RealSet ⇒ f(x) = cases{ x if |x| ≤ 1; 1 if |x| > 1 }
3. lim_{ x → (-1)^- } (f(x)) = 1
4. lim_{ x → (-1)^+ } (f(x)) = -1
5. ¬ContinuousFuncAt(f, -1)
6. JumpSingularPoint(f, -1)

GOAL:
JumpSingularPoint(f, -1)

METHOD:

-/
theorem proof_gap_exercise_731_3_5
  (f : ℝ → ℝ)
  (h1 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) → f x = if |x| ≤ 1 then x else 1)
  (h2 : Tendsto f (𝓝[<] (-1 : ℝ)) (𝓝 (1 : ℝ)))
  (h3 : Tendsto f (𝓝[>] (-1 : ℝ)) (𝓝 (-1 : ℝ)))
  (h4 : ¬ ContinuousAt f (-1 : ℝ))
  (h5 : Exercise731_3.JumpSingularPoint f (-1 : ℝ))
  : Exercise731_3.JumpSingularPoint f (-1 : ℝ) := by
  sorry

