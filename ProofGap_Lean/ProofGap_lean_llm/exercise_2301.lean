import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Exercise2301

-- Riemann integrability on a compact interval, via Lebesgue's criterion:
-- boundedness and continuity relative to the interval almost everywhere.
def RiemannIntegrableOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  BddAbove (f '' Set.Icc a b) ∧ BddBelow (f '' Set.Icc a b) ∧
    ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), ContinuousWithinAt f (Set.Icc a b) x

-- Finite, unequal one-sided limits define a jump discontinuity.
def JumpSingularPoint (F : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ l r : ℝ, Tendsto F (𝓝[<] x) (𝓝 l) ∧
    Tendsto F (𝓝[>] x) (𝓝 r) ∧ l ≠ r

noncomputable def leftLimit (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder (𝓝[<] x) F

noncomputable def rightLimit (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder (𝓝[>] x) F

noncomputable def integralSum (f : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (η : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1), ∫ x in (c i + η)..(c (i + 1) - η), f x

noncomputable def differenceSum (F : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (η : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1), (F (c (i + 1) - η) - F (c i + η))

noncomputable def limitSum (F : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1), (leftLimit F (c (i + 1)) - rightLimit F (c i))

noncomputable def correctedDifference (F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  leftLimit F b - rightLimit F a -
    ∑ i ∈ Finset.Icc 1 p, (rightLimit F (c i) - leftLimit F (c i))

end Exercise2301
open Exercise2301

/- Exercise 2301, gap 1
SHA-256: c32d3f94534eacebc00944044921fe28df7f428a11fa0ef9bed14abe2e726a02
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))

GOAL:
DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))

METHOD:

-/
theorem proof_gap_exercise_2301_1
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p) := by
  sorry

/- Exercise 2301, gap 2
SHA-256: 9588fe3ea6096690ec6f0e61ba3a4060a17bec7dc3f97633b23c661acf5c45f5
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))
16. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))

GOAL:
forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [c(i) + η, c(i + 1) - η] ⇒ FunDeri(F, 1, 1)(x) = f(x)))

METHOD:

-/
theorem proof_gap_exercise_2301_2
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  (h16 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p))
  : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    ∀ x : ℝ, x ∈ Set.Icc (c i + η) (c (i + 1) - η) → HasDerivAt F (f x) x := by
  sorry

/- Exercise 2301, gap 3
SHA-256: ace3d73d1965fa4f54e93c03ffac0a1a88652fc0426cebd75ffe0ac62890c37c
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))
16. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))
17. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [c(i) + η, c(i + 1) - η] ⇒ FunDeri(F, 1, 1)(x) = f(x)))

GOAL:
forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = F(c(i + 1) - η) - F(c(i) + η))

METHOD:
[@method 根据 "牛顿-莱布尼茨公式" @]
-/
theorem proof_gap_exercise_2301_3
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  (h16 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p))
  (h17 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    ∀ x : ℝ, x ∈ Set.Icc (c i + η) (c (i + 1) - η) → HasDerivAt F (f x) x)
  : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    (∫ x in (c i + η)..(c (i + 1) - η), f x) = F (c (i + 1) - η) - F (c i + η) := by
  sorry

/- Exercise 2301, gap 4
SHA-256: bdd0e98284d7f3cb1ec41009775208e2b56d4da0ff30c156c75880e1e1995dbb
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))
16. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))
17. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [c(i) + η, c(i + 1) - η] ⇒ FunDeri(F, 1, 1)(x) = f(x)))
18. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = F(c(i + 1) - η) - F(c(i) + η))

GOAL:
DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η)))

METHOD:

-/
theorem proof_gap_exercise_2301_4
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  (h16 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p))
  (h17 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    ∀ x : ℝ, x ∈ Set.Icc (c i + η) (c (i + 1) - η) → HasDerivAt F (f x) x)
  (h18 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    (∫ x in (c i + η)..(c (i + 1) - η), f x) = F (c (i + 1) - η) - F (c i + η))
  : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p) := by
  sorry

/- Exercise 2301, gap 5
SHA-256: 72790ddd50ff623cead2984bc6b494d7278a74e0e9c94abf464e774a50795043
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))
16. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))
17. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [c(i) + η, c(i + 1) - η] ⇒ FunDeri(F, 1, 1)(x) = f(x)))
18. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = F(c(i + 1) - η) - F(c(i) + η))
19. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η)))

GOAL:
lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η))) = sum_{ i = 0 }^{ p } ((lim_{ x → c(i + 1)^- } (F(x))) - (lim_{ x → c(i)^+ } (F(x))))

METHOD:

-/
theorem proof_gap_exercise_2301_5
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  (h16 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p))
  (h17 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    ∀ x : ℝ, x ∈ Set.Icc (c i + η) (c (i + 1) - η) → HasDerivAt F (f x) x)
  (h18 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    (∫ x in (c i + η)..(c (i + 1) - η), f x) = F (c (i + 1) - η) - F (c i + η))
  (h19 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p))
  : limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p) = limitSum F c p := by
  sorry

/- Exercise 2301, gap 6
SHA-256: a6e994d22e8151691a0b63f2eaf601009c4acc85c818fe2a4b3c3086effbc871
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))
16. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))
17. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [c(i) + η, c(i + 1) - η] ⇒ FunDeri(F, 1, 1)(x) = f(x)))
18. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = F(c(i + 1) - η) - F(c(i) + η))
19. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η)))
20. lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η))) = sum_{ i = 0 }^{ p } ((lim_{ x → c(i + 1)^- } (F(x))) - (lim_{ x → c(i)^+ } (F(x))))

GOAL:
sum_{ i = 0 }^{ p } ((lim_{ x → c(i + 1)^- } (F(x))) - (lim_{ x → c(i)^+ } (F(x)))) = (lim_{ x → b^- } (F(x))) - (lim_{ x → a^+ } (F(x))) - (sum_{ i = 1 }^{ p } ((lim_{ x → c(i)^+ } (F(x))) - (lim_{ x → c(i)^- } (F(x)))))

METHOD:

-/
theorem proof_gap_exercise_2301_6
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  (h16 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p))
  (h17 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    ∀ x : ℝ, x ∈ Set.Icc (c i + η) (c (i + 1) - η) → HasDerivAt F (f x) x)
  (h18 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    (∫ x in (c i + η)..(c (i + 1) - η), f x) = F (c (i + 1) - η) - F (c i + η))
  (h19 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p))
  (h20 : limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p) = limitSum F c p)
  : limitSum F c p = correctedDifference F a b c p := by
  sorry

/- Exercise 2301, gap 7
SHA-256: a112985da0c491ba714d7c0ef2204d1902683824fab851c99877461e223f83d4
PROOF GAP @7
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))
16. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))
17. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [c(i) + η, c(i + 1) - η] ⇒ FunDeri(F, 1, 1)(x) = f(x)))
18. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = F(c(i + 1) - η) - F(c(i) + η))
19. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η)))
20. lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η))) = sum_{ i = 0 }^{ p } ((lim_{ x → c(i + 1)^- } (F(x))) - (lim_{ x → c(i)^+ } (F(x))))
21. sum_{ i = 0 }^{ p } ((lim_{ x → c(i + 1)^- } (F(x))) - (lim_{ x → c(i)^+ } (F(x)))) = (lim_{ x → b^- } (F(x))) - (lim_{ x → a^+ } (F(x))) - (sum_{ i = 1 }^{ p } ((lim_{ x → c(i)^+ } (F(x))) - (lim_{ x → c(i)^- } (F(x)))))

GOAL:
DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = (lim_{ x → b^- } (F(x))) - (lim_{ x → a^+ } (F(x))) - (sum_{ i = 1 }^{ p } ((lim_{ x → c(i)^+ } (F(x))) - (lim_{ x → c(i)^- } (F(x)))))

METHOD:

-/
theorem proof_gap_exercise_2301_7
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  (h16 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p))
  (h17 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    ∀ x : ℝ, x ∈ Set.Icc (c i + η) (c (i + 1) - η) → HasDerivAt F (f x) x)
  (h18 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    (∫ x in (c i + η)..(c (i + 1) - η), f x) = F (c (i + 1) - η) - F (c i + η))
  (h19 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p))
  (h20 : limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p) = limitSum F c p)
  (h21 : limitSum F c p = correctedDifference F a b c p)
  : (∫ x in a..b, f x) = correctedDifference F a b c p := by
  sorry

/- Exercise 2301, gap 8
SHA-256: d66bdb914a2a79d0c11637c17e353785edf21f8eff37b1da1c89a52640a0e98b
PROOF GAP @8
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. a ∈ RealSet
4. b ∈ RealSet
5. c : NonNegIntegerSet → RealSet
6. p ∈ NonNegIntegerSet ∧ p > 0
7. a < b
8. p ∈ PosIntegerSet
9. IntegrableFuncOn(f, [a, b])
10. c(0) = a
11. c(p + 1) = b
12. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ a < c(i) ∧ c(i) < b
13. forall (i), i ∈ NonNegIntegerSet ∧ i ≤ p ⇒ c(i) < c(i + 1)
14. forall (x), x ∈ RealSet ∧ x ∈ [a, b] ∧ (forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ x ≠ c(i)) ∧ x ≠ a ∧ x ≠ b ⇒ FunDeri(F, 1, 1)(x) = f(x)
15. forall (i), i ∈ NonNegIntegerSet ∧ i ∈ PosIntegerSet ∧ i ≤ p ⇒ JumpSingularPoint(F, c(i))
16. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x))))
17. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [c(i) + η, c(i + 1) - η] ⇒ FunDeri(F, 1, 1)(x) = f(x)))
18. forall (η), η ∈ RealSet ⇒ (forall (i), η > 0 ∧ i ∈ NonNegIntegerSet ∧ i ≤ p ∧ η < frac(c(i + 1) - c(i), 2) ⇒ DefInt(c(i) + η, c(i + 1) - η, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = F(c(i + 1) - η) - F(c(i) + η))
19. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η)))
20. lim_{ η → 0^+ } (sum_{ i = 0 }^{ p } (F(c(i + 1) - η) - F(c(i) + η))) = sum_{ i = 0 }^{ p } ((lim_{ x → c(i + 1)^- } (F(x))) - (lim_{ x → c(i)^+ } (F(x))))
21. sum_{ i = 0 }^{ p } ((lim_{ x → c(i + 1)^- } (F(x))) - (lim_{ x → c(i)^+ } (F(x)))) = (lim_{ x → b^- } (F(x))) - (lim_{ x → a^+ } (F(x))) - (sum_{ i = 1 }^{ p } ((lim_{ x → c(i)^+ } (F(x))) - (lim_{ x → c(i)^- } (F(x)))))
22. DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = (lim_{ x → b^- } (F(x))) - (lim_{ x → a^+ } (F(x))) - (sum_{ i = 1 }^{ p } ((lim_{ x → c(i)^+ } (F(x))) - (lim_{ x → c(i)^- } (F(x)))))

GOAL:
DefInt(a, b, (fun x [x ∈ RealSet] . f(x)) * diff(fun x [x ∈ RealSet] . x)) = (lim_{ x → b^- } (F(x))) - (lim_{ x → a^+ } (F(x))) - (sum_{ i = 1 }^{ p } ((lim_{ x → c(i)^+ } (F(x))) - (lim_{ x → c(i)^- } (F(x)))))

METHOD:

-/
theorem proof_gap_exercise_2301_8
  (f F : ℝ → ℝ) (a b : ℝ) (c : ℕ → ℝ) (p : ℕ)
  (h6 : p > 0)
  (h7 : a < b)
  (h8 : 0 < p)
  (h9 : RiemannIntegrableOn f a b)
  (h10 : c 0 = a)
  (h11 : c (p + 1) = b)
  (h12 : ∀ i : ℕ, 0 < i → i ≤ p → a < c i ∧ c i < b)
  (h13 : ∀ i : ℕ, i ≤ p → c i < c (i + 1))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc a b →
    (∀ i : ℕ, 0 < i → i ≤ p → x ≠ c i) →
    x ≠ a → x ≠ b → HasDerivAt F (f x) x)
  (h15 : ∀ i : ℕ, 0 < i → i ≤ p → JumpSingularPoint F (c i))
  (h16 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (integralSum f c p))
  (h17 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    ∀ x : ℝ, x ∈ Set.Icc (c i + η) (c (i + 1) - η) → HasDerivAt F (f x) x)
  (h18 : ∀ η : ℝ, ∀ i : ℕ, η > 0 → i ≤ p → η < (c (i + 1) - c i) / 2 →
    (∫ x in (c i + η)..(c (i + 1) - η), f x) = F (c (i + 1) - η) - F (c i + η))
  (h19 : (∫ x in a..b, f x) = limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p))
  (h20 : limUnder (𝓝[>] (0 : ℝ)) (differenceSum F c p) = limitSum F c p)
  (h21 : limitSum F c p = correctedDifference F a b c p)
  (h22 : (∫ x in a..b, f x) = correctedDifference F a b c p)
  : (∫ x in a..b, f x) = correctedDifference F a b c p := by
  sorry
