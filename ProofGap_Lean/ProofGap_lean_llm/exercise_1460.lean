import Mathlib

set_option linter.unusedVariables false

namespace Exercise1460

-- Set of global minimizers on the specified set (source Thm 225).
def minimumPointsOn (f : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {x | x ∈ s ∧ ∀ y ∈ s, f x ≤ f y}

end Exercise1460

open Exercise1460

/- Exercise 1460, gap 1
SHA-256: c1e05175d4ed3519d1645d8c3fff0b4bdaa97bf02cf9f6fb8e805e862ee9662a
PROOF GAP @1
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)

METHOD:

-/
theorem proof_gap_exercise_1460_1
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b) := by
  sorry

/- Exercise 1460, gap 2
SHA-256: 81e9e3fb1e8bdcea8b83a39accec089dbeaec3574e083a32effbae17c74ffead
PROOF GAP @2
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})

METHOD:

-/
theorem proof_gap_exercise_1460_2
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂) := by
  sorry

/- Exercise 1460, gap 3
SHA-256: 58a01443196f0ed0b4a4a2da84de21a4dcf3461b2e03e5b2501d42744eddd362
PROOF GAP @3
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})

GOAL:
forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))

METHOD:

-/
theorem proof_gap_exercise_1460_3
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2) := by
  sorry

/- Exercise 1460, gap 4
SHA-256: 59456009211d0ca0db2ab5be8a7b6b93b584631a51d55cb5f2c28df3db4a1936
PROOF GAP @4
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0

METHOD:

-/
theorem proof_gap_exercise_1460_4
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0 := by
  sorry

/- Exercise 1460, gap 5
SHA-256: 3c2bbb29579bed6c1bf616841ea61672ce86d6d114a9add037cf5304d3d5b208
PROOF GAP @5
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0

GOAL:
MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }

METHOD:

-/
theorem proof_gap_exercise_1460_5
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ) := by
  sorry

/- Exercise 1460, gap 6
SHA-256: 1938b4f5ae07094d6941c11e6d7d483ac4b27444b9be94117dd5e1f5f24172d6
PROOF GAP @6
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }

GOAL:
Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })

METHOD:

-/
theorem proof_gap_exercise_1460_6
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|) := by
  sorry

/- Exercise 1460, gap 7
SHA-256: 8f31eb614aa6d02abf5ff57fe65b54b63f2cf01733806855057b315bfb2fa311
PROOF GAP @7
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })

GOAL:
Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })

METHOD:

-/
theorem proof_gap_exercise_1460_7
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂| := by
  sorry

/- Exercise 1460, gap 8
SHA-256: 9976f3214bcb4dcd9fa61f3d2d195ddcb633e9e7588134f7d8ad049538d66cf1
PROOF GAP @8
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })
17. Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })

GOAL:
forall (c), c ∈ RealSet ∧ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}| ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })

METHOD:

-/
theorem proof_gap_exercise_1460_8
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  (h17 : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂|)
  : ∀ c : ℝ, (|b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)) := by
  sorry

/- Exercise 1460, gap 9
SHA-256: 883f05b1f53126b7f051fb88f4c304914778db8bbeffc7f51a4b33752e4af4cc
PROOF GAP @9
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })
17. Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })
18. forall (c), c ∈ RealSet ∧ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}| ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })

GOAL:
b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}|

METHOD:

-/
theorem proof_gap_exercise_1460_9
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  (h17 : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂|)
  (h18 : ∀ c : ℝ, (|b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → |b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂| := by
  sorry

/- Exercise 1460, gap 10
SHA-256: d7f2a3a6fc47aa06a27f61a2256071e0f2c399fb3baa891dc3684b1572c9b215
PROOF GAP @10
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })
17. Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })
18. forall (c), c ∈ RealSet ∧ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}| ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
19. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}|

GOAL:
forall (c), c ∈ RealSet ∧ b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })

METHOD:

-/
theorem proof_gap_exercise_1460_10
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  (h17 : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂|)
  (h18 : ∀ c : ℝ, (|b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h19 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → |b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|)
  : ∀ c : ℝ, b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)) := by
  sorry

/- Exercise 1460, gap 11
SHA-256: abdcc2c313d02e3cc43b34d7e996d13dfaf4daa82477752385f02f12db44b845
PROOF GAP @11
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })
17. Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })
18. forall (c), c ∈ RealSet ∧ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}| ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
19. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}|
20. forall (c), c ∈ RealSet ∧ b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })

GOAL:
b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8)

METHOD:

-/
theorem proof_gap_exercise_1460_11
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  (h17 : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂|)
  (h18 : ∀ c : ℝ, (|b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h19 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → |b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|)
  (h20 : ∀ c : ℝ, b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) := by
  sorry

/- Exercise 1460, gap 12
SHA-256: 2271eddefeac05d3814e0ab542853d1c8957ffd5c05b72e41b275ff11fbdfc9e
PROOF GAP @12
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })
17. Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })
18. forall (c), c ∈ RealSet ∧ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}| ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
19. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}|
20. forall (c), c ∈ RealSet ∧ b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
21. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8)

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x - frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8)

METHOD:

-/
theorem proof_gap_exercise_1460_12
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  (h17 : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂|)
  (h18 : ∀ c : ℝ, (|b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h19 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → |b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|)
  (h20 : ∀ c : ℝ, b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h21 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8))
  : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x - (x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8 := by
  sorry

/- Exercise 1460, gap 13
SHA-256: 3ecfbbb41b41a53130ea90a791914cb9776855e7447a44c5988db163e77a5db6
PROOF GAP @13
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })
17. Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })
18. forall (c), c ∈ RealSet ∧ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}| ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
19. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}|
20. forall (c), c ∈ RealSet ∧ b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
21. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8)
22. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x - frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8)

GOAL:
Δ = frac((x_{1} - x_{2})^{2}, 8)

METHOD:

-/
theorem proof_gap_exercise_1460_13
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  (h17 : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂|)
  (h18 : ∀ c : ℝ, (|b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h19 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → |b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|)
  (h20 : ∀ c : ℝ, b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h21 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8))
  (h22 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x - (x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8)
  : Δ = ((x₁ - x₂) ^ 2 / 8) := by
  sorry

/- Exercise 1460, gap 14
SHA-256: 236c717328a80c87927d8b5d24e18d8fe12dc2ce8c2ac6206ffdaf7dd8283bfb
PROOF GAP @14
ASSUM:
1. x_{1} ∈ RealSet
2. x_{2} ∈ RealSet
3. b ∈ RealSet
4. f : RealSet → RealSet
5. g : RealSet → RealSet
6. Δ ∈ RealSet
7. x_{1} ≤ x_{2}
8. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) = x^{2}
9. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x + b
10. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ Δ = sup({ |f(x) - g(x)| | x ∈ [x_{1}, x_{2}] })
11. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ f(x) - g(x) = x^{2} - ((x_{1} + x_{2}) * x + b)
12. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 2 * x - (x_{1} + x_{2})
13. forall (x), x ∈ RealSet ⇒ (FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x) = 0 ⇔ x = frac(x_{1} + x_{2}, 2))
14. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ FunDeri(f, 1, 2)(x) - FunDeri(g, 1, 2)(x) = 2 ∧ 2 > 0
15. MinimumPointOn(f - g, [x_{1}, x_{2}]) = { frac(x_{1} + x_{2}, 2) }
16. Δ = max({ |f(frac(x_{1} + x_{2}, 2)) - g(frac(x_{1} + x_{2}, 2))|, |f(x_{1}) - g(x_{1})|, |f(x_{2}) - g(x_{2})| })
17. Δ = max({ |b + frac((x_{1} + x_{2})^{2}, 4)|, |b + x_{1} * x_{2}| })
18. forall (c), c ∈ RealSet ∧ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}| ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
19. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ |b + frac((x_{1} + x_{2})^{2}, 4)| = |b + x_{1} * x_{2}|
20. forall (c), c ∈ RealSet ∧ b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8) ⇒ Δ = min({ max({ |c + frac((x_{1} + x_{2})^{2}, 4)|, |c + x_{1} * x_{2}| }) | c ∈ RealSet })
21. b = -frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8)
22. forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ g(x) = (x_{1} + x_{2}) * x - frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8)
23. Δ = frac((x_{1} - x_{2})^{2}, 8)

GOAL:
(b, Δ) = (-frac((x_{1})^{2} + (x_{2})^{2} + 6 * x_{1} * x_{2}, 8), frac((x_{1} - x_{2})^{2}, 8)) ⇒ (forall (c), c ∈ RealSet ⇒ (forall (x), x ∈ RealSet ∧ x ∈ [x_{1}, x_{2}] ⇒ sup({ |x^{2} - ((x_{1} + x_{2}) * x + b)| | x ∈ [x_{1}, x_{2}] }) ≤ sup({ |x^{2} - ((x_{1} + x_{2}) * x + c)| | x ∈ [x_{1}, x_{2}] })))

METHOD:

-/
theorem proof_gap_exercise_1460_14
  (x₁ x₂ b : ℝ) (f g : ℝ → ℝ) (Δ : ℝ)
  (h7 : x₁ ≤ x₂)
  (h8 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x = x ^ 2)
  (h9 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x + b)
  (h10 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → Δ = sSup ((fun t : ℝ => |f t - g t|) '' Set.Icc x₁ x₂))
  (h11 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → f x - g x = x ^ 2 - ((x₁ + x₂) * x + b))
  (h12 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 1 f x - iteratedDeriv 1 g x = 2 * x - (x₁ + x₂))
  (h13 : ∀ x : ℝ, iteratedDeriv 1 f x - iteratedDeriv 1 g x = 0 ↔ x = ((x₁ + x₂) / 2))
  (h14 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → iteratedDeriv 2 f x - iteratedDeriv 2 g x = 2 ∧ (2 : ℝ) > 0)
  (h15 : minimumPointsOn (fun x => f x - g x) (Set.Icc x₁ x₂) = ({((x₁ + x₂) / 2)} : Set ℝ))
  (h16 : Δ = max |f ((x₁ + x₂) / 2) - g ((x₁ + x₂) / 2)| (max |f x₁ - g x₁| |f x₂ - g x₂|))
  (h17 : Δ = max |b + ((x₁ + x₂) ^ 2 / 4)| |b + x₁ * x₂|)
  (h18 : ∀ c : ℝ, (|b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h19 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → |b + ((x₁ + x₂) ^ 2 / 4)| = |b + x₁ * x₂|)
  (h20 : ∀ c : ℝ, b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8) → Δ = sInf (Set.range (fun t : ℝ => max |t + ((x₁ + x₂) ^ 2 / 4)| |t + x₁ * x₂|)))
  (h21 : b = (-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8))
  (h22 : ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ → g x = (x₁ + x₂) * x - (x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8)
  (h23 : Δ = ((x₁ - x₂) ^ 2 / 8))
  : (b, Δ) = ((-(x₁ ^ 2 + x₂ ^ 2 + 6 * x₁ * x₂) / 8), ((x₁ - x₂) ^ 2 / 8)) → ∀ c : ℝ, ∀ x : ℝ, x ∈ Set.Icc x₁ x₂ →
    sSup ((fun t : ℝ => |t ^ 2 - ((x₁ + x₂) * t + b)|) '' Set.Icc x₁ x₂) ≤ sSup ((fun t : ℝ => |t ^ 2 - ((x₁ + x₂) * t + c)|) '' Set.Icc x₁ x₂) := by
  sorry
