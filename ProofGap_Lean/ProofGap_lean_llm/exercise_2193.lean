import Mathlib

open scoped BigOperators Topology
open Filter

/- This file preserves the printed gaps, including their source scope defects.
The fixed sequences are NOT silently replaced by a family of partitions.
Consequently the printed d-limit has a constant body. See the review JSON.
Only the fourteen main theorem proofs are placeholders. -/
namespace Exercise2193

noncomputable def sumTerms (n : ℕ) (g : ℤ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1), g j

noncomputable def mesh (n : ℕ) (dx : ℤ → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 ∧ r = |dx j|}

end Exercise2193
open Exercise2193

/- Exercise 2193, gap 1
SHA256: 3b972c19d965ba9f5588c12bb7b564e628d1b24524a6d1cb7bfcc2a03785dd81
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })

GOAL:
ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])

METHOD:

-/
theorem proof_gap_exercise_2193_1
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  : ContinuousOn (fun t => f t * φ t) (Set.Icc a b) := by
  sorry

/- Exercise 2193, gap 2
SHA256: 6e7733569fe72305b2fa33d9107ce5708d97968a26f81031478ae63059e49c8b
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])

GOAL:
DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))

METHOD:

-/
theorem proof_gap_exercise_2193_2
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)) := by
  sorry

/- Exercise 2193, gap 3
SHA256: fe7eaca694c36d9f3f5c68a7bce8ed4f4e0a7c2b6f4b50f4db9591cc112b6495
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))

GOAL:
BoundedFuncOn(f, [a, b])

METHOD:

-/
theorem proof_gap_exercise_2193_3
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C := by
  sorry

/- Exercise 2193, gap 4
SHA256: 91e53fcf72c51adbc21ea3c43051cb90ba914587e8da4a0f33255e5adfa20909
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])

GOAL:
exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)

METHOD:

-/
theorem proof_gap_exercise_2193_4
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C) := by
  sorry

/- Exercise 2193, gap 5
SHA256: 6ff5d520fe144ce7dc8dee5ca297529d1fba1530730d65c2110104917367de62
PROOF GAP @5
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)

GOAL:
UniformContinuousFuncOn(φ, [a, b])

METHOD:

-/
theorem proof_gap_exercise_2193_5
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  : UniformContinuousOn φ (Set.Icc a b) := by
  sorry

/- Exercise 2193, gap 6
SHA256: 4c6f0dd134909a7c63e04091335ea5fbc54f658fbafe550d2ef9db07acd51536
PROOF GAP @6
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))

METHOD:

-/
theorem proof_gap_exercise_2193_6
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))) := by
  sorry

/- Exercise 2193, gap 7
SHA256: d8cab108372897e444ed6e4075c0212a5914a832c25d452a6d36c4d529757c67
PROOF GAP @7
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)

METHOD:

-/
theorem proof_gap_exercise_2193_7
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) := by
  sorry

/- Exercise 2193, gap 8
SHA256: 7d037d933e731d5f01553711df5d5b3bc6c505a4d8c629e9b5b59aa3f4f8474d
PROOF GAP @8
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|)

METHOD:

-/
theorem proof_gap_exercise_2193_8
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  (h29 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|))
  : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|) := by
  sorry

/- Exercise 2193, gap 9
SHA256: e5374366950b4b035e9a323fd21ec57a4cb3cd44673725448428535ab60ef6b6
PROOF GAP @9
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|) = ε

METHOD:

-/
theorem proof_gap_exercise_2193_9
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  (h29 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|))
  (h30 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|))
  : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|) = ε := by
  sorry

/- Exercise 2193, gap 10
SHA256: 0ce5f59d5c6eb8f88f78a30d17834091bd28269f53628d37fbc210de1388c88b
PROOF GAP @10
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|)
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|) = ε

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < ε

METHOD:

-/
theorem proof_gap_exercise_2193_10
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  (h29 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|))
  (h30 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|))
  (h31 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|) = ε)
  : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < ε := by
  sorry

/- Exercise 2193, gap 11
SHA256: e5f6da9424a0700b9543ae1063143ad58cbe6c9b6e70a3e60e0b34c1228c073f
PROOF GAP @11
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|)
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|) = ε
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < ε

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| < ε

METHOD:

-/
theorem proof_gap_exercise_2193_11
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  (h29 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|))
  (h30 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|))
  (h31 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|) = ε)
  (h32 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < ε)
  : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| < ε := by
  sorry

/- Exercise 2193, gap 12
SHA256: f0822578320cac08171d3230a730eb13d2979fd7e0b1048b9b35bfddf095b5f3
PROOF GAP @12
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|)
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|) = ε
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < ε
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| < ε

GOAL:
lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))) = 0

METHOD:

-/
theorem proof_gap_exercise_2193_12
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  (h29 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|))
  (h30 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|))
  (h31 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|) = ε)
  (h32 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < ε)
  (h33 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| < ε)
  : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry

/- Exercise 2193, gap 13
SHA256: cf7a8d9afc32d45f7f4bb63b8ba10d6fa279fe728ed6623fde6a763bcb18f32e
PROOF GAP @13
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|)
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|) = ε
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < ε
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| < ε
34. lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))) = 0

GOAL:
lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(θ(i)) * Δx(i))) = DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t))

METHOD:

-/
theorem proof_gap_exercise_2193_13
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  (h29 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|))
  (h30 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|))
  (h31 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|) = ε)
  (h32 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < ε)
  (h33 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| < ε)
  (h34 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (θ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)) := by
  sorry

/- Exercise 2193, gap 14
SHA256: ee3fcb74e1a05f578855c1c120878cca13bf3c2e28031530ead7b6285ec86a4d
PROOF GAP @14
ASSUM:
1. a ∈ RealSet
2. b ∈ RealSet
3. f : RealSet → RealSet
4. φ : RealSet → RealSet
5. x : NonNegIntegerSet → RealSet
6. ξ : IntegerSet → RealSet
7. θ : IntegerSet → RealSet
8. Δx : IntegerSet → RealSet
9. d ∈ RealSet ∧ d > 0
10. n ∈ NonNegIntegerSet ∧ n > 0
11. i ∈ IntegerSet
12. M ∈ RealSet ∧ M > 0
13. δ ∈ RealSet ∧ δ > 0
14. a < b
15. ContinuousFuncOn(f, [a, b])
16. ContinuousFuncOn(φ, [a, b])
17. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n ⇒ x(i) ∈ [a, b]
18. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) < x(i + 1)
19. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ x(i) ≤ ξ(i) ∧ ξ(i) ≤ x(i + 1) ∧ x(i) ≤ θ(i) ∧ θ(i) ≤ x(i + 1)
20. forall (n) (i), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ∧ i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ Δx(i) = x(i + 1) - x(i)
21. forall (n), n ∈ NonNegIntegerSet ∧ n > 0 ∧ n ∈ PosIntegerSet ⇒ x(0) = a ∧ x(n) = b
22. d = max({ |Δx(i)| | i ∈ IntegerSet, 0 ≤ i ∧ i ≤ n - 1 })
23. ContinuousFuncOn(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t), [a, b])
24. DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t)) = lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(ξ(i)) * Δx(i)))
25. BoundedFuncOn(f, [a, b])
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ M ∈ PosRealSet ∧ (forall (t), t ∈ RealSet ∧ t ∈ [a, b] ⇒ |f(t)| ≤ M)
27. UniformContinuousFuncOn(φ, [a, b])
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (d < δ ⇒ (forall (i), i ∈ IntegerSet ∧ 0 ≤ i ∧ i ≤ n - 1 ⇒ |φ(θ(i)) - φ(ξ(i))| < frac(ε, M * (b - a)))))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| ≤ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|)
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|)
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (M * frac(ε, M * (b - a)) * |Δx(i)|) = ε
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ sum_{ i = 0 }^{ n - 1 } (|f(ξ(i))| * |φ(θ(i)) - φ(ξ(i))| * |Δx(i)|) < ε
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ∧ d < δ ⇒ |sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))| < ε
34. lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } ((f(ξ(i)) * φ(θ(i)) - f(ξ(i)) * φ(ξ(i))) * Δx(i))) = 0
35. lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(θ(i)) * Δx(i))) = DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t))

GOAL:
lim_{ d → 0 } (sum_{ i = 0 }^{ n - 1 } (f(ξ(i)) * φ(θ(i)) * Δx(i))) = DefInt(a, b, fun t [t ∈ RealSet ∧ t ∈ [a, b]] . f(t) * φ(t) * diff(fun t [t ∈ RealSet ∧ t ∈ [a, b]] . t))

METHOD:

-/
theorem proof_gap_exercise_2193_14
  (a b : ℝ) (f φ : ℝ → ℝ) (x : ℕ → ℝ)
  (ξ θ Δx : ℤ → ℝ) (d : ℝ) (n : ℕ) (i : ℤ) (M δ : ℝ)
  (h9 : 0 < d) (h10 : 0 < n) (h12 : 0 < M) (h13 : 0 < δ)
  (h14 : a < b)
  (h15 : ContinuousOn f (Set.Icc a b))
  (h16 : ContinuousOn φ (Set.Icc a b))
  (h17 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) →
    x j.toNat ∈ Set.Icc a b)
  (h18 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat < x (j + 1).toNat)
  (h19 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    x j.toNat ≤ ξ j ∧ ξ j ≤ x (j + 1).toNat ∧
    x j.toNat ≤ θ j ∧ θ j ≤ x (j + 1).toNat)
  (h20 : ∀ (k : ℕ) (j : ℤ), 0 < k ∧ 0 ≤ j ∧ j ≤ (k : ℤ) - 1 →
    Δx j = x (j + 1).toNat - x j.toNat)
  (h21 : ∀ k : ℕ, 0 < k → x 0 = a ∧ x k = b)
  (h22 : d = mesh n Δx)
  (h23 : ContinuousOn (fun t => f t * φ t) (Set.Icc a b))
  (h24 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (ξ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  (h25 : ∃ C : ℝ, ∀ t ∈ Set.Icc a b, |f t| ≤ C)
  (h26 : ∃ C : ℝ, 0 < C ∧ (∀ t ∈ Set.Icc a b, |f t| ≤ C))
  (h27 : UniformContinuousOn φ (Set.Icc a b))
  (h28 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ (d < η → ∀ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ) - 1 → |φ (θ j) - φ (ξ j)| < ε / (M * (b - a))))
  (h29 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| ≤ sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|))
  (h30 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|))
  (h31 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => M * (ε / (M * (b - a))) * |Δx j|) = ε)
  (h32 : ∀ ε : ℝ, 0 < ε ∧ d < δ → sumTerms n (fun j => |f (ξ j)| * |φ (θ j) - φ (ξ j)| * |Δx j|) < ε)
  (h33 : ∀ ε : ℝ, 0 < ε ∧ d < δ → |sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)| < ε)
  (h34 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => (f (ξ j) * φ (θ j) - f (ξ j) * φ (ξ j)) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)))
  (h35 : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (θ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)))
  : Tendsto (fun (_d : ℝ) => sumTerms n (fun j => f (ξ j) * φ (θ j) * Δx j)) (𝓝[≠] (0 : ℝ)) (𝓝 (∫ t in a..b, f t * φ t)) := by
  sorry

