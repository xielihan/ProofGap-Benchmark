import Mathlib

open Filter
open scoped Topology

-- Equality of two existing finite, two-sided punctured limits.
def exercise1015SameLimit (u v : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Tendsto u (𝓝[≠] (0 : ℝ)) (𝓝 L) ∧
    Tendsto v (𝓝[≠] (0 : ℝ)) (𝓝 L)

-- Domain defined as the projection of the graph (source Thm 220).
def exercise1015Dom (u : ℝ → ℝ) : Set ℝ :=
  {x | ∃ y : ℝ, u x = y}

/- Exercise 1015_1, gap 1
SHA-256: 4ae4054c58002709bd3765ded26def17f9d6c01576e30a449a4e3f237103740d
PROOF GAP @1
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)

GOAL:
DiffableFuncAt(f, 0)

METHOD:

-/
theorem proof_gap_exercise_1015_1_1
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  : DifferentiableAt ℝ f 0 := by
  sorry

/- Exercise 1015_1, gap 2
SHA-256: ba1e6f47b714d6d3b519beaf6e5061b39a80d68ea3b3f84658acd14de2c54cbc
PROOF GAP @2
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)

GOAL:
FunDeri(f, 1, 1)(0) = 1

METHOD:

-/
theorem proof_gap_exercise_1015_1_2
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  : deriv f 0 = 1 := by
  sorry

/- Exercise 1015_1, gap 3
SHA-256: fa866742b3a20e71984f7f64715cfdad67c444b291997174382fb7a0fd628048
PROOF GAP @3
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1

GOAL:
¬DiffableFuncAt(g, 0)

METHOD:

-/
theorem proof_gap_exercise_1015_1_3
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  : ¬ DifferentiableAt ℝ g 0 := by
  sorry

/- Exercise 1015_1, gap 4
SHA-256: 3139c4f5219e99411e8f52c5fecdae32a757c7386c5cd285ce8b18a8d6ee955b
PROOF GAP @4
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1
7. ¬DiffableFuncAt(g, 0)

GOAL:
lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx))

METHOD:

-/
theorem proof_gap_exercise_1015_1_4
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  (h7 : ¬ DifferentiableAt ℝ g 0)
  : exercise1015SameLimit (fun x : ℝ => (F x - F 0) / x) (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x) := by
  sorry

/- Exercise 1015_1, gap 5
SHA-256: eee926b9fcf17baa55244d6359c3fd085ce95aa2e06ee3ecdd4a460f97e32a35
PROOF GAP @5
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1
7. ¬DiffableFuncAt(g, 0)
8. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx))

GOAL:
lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx)) = lim_{ Δx → 0 } (|Δx|)

METHOD:

-/
theorem proof_gap_exercise_1015_1_5
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  (h7 : ¬ DifferentiableAt ℝ g 0)
  (h8 : exercise1015SameLimit (fun x : ℝ => (F x - F 0) / x) (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x))
  : exercise1015SameLimit (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x) (fun x : ℝ => |x|) := by
  sorry

/- Exercise 1015_1, gap 6
SHA-256: 9f37fc91c21d2c6d2964e688a90b0c14564ee87f6ddb60c335f3d41b19540f69
PROOF GAP @6
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1
7. ¬DiffableFuncAt(g, 0)
8. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx))
9. lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx)) = lim_{ Δx → 0 } (|Δx|)

GOAL:
lim_{ Δx → 0 } (|Δx|) = 0

METHOD:

-/
theorem proof_gap_exercise_1015_1_6
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  (h7 : ¬ DifferentiableAt ℝ g 0)
  (h8 : exercise1015SameLimit (fun x : ℝ => (F x - F 0) / x) (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x))
  (h9 : exercise1015SameLimit (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x) (fun x : ℝ => |x|))
  : Tendsto (fun x : ℝ => |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  sorry

/- Exercise 1015_1, gap 7
SHA-256: 9b0bea761bcea9d4be9c0c5ab288da6798cf755680e926188499f81591de263a
PROOF GAP @7
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1
7. ¬DiffableFuncAt(g, 0)
8. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx))
9. lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx)) = lim_{ Δx → 0 } (|Δx|)
10. lim_{ Δx → 0 } (|Δx|) = 0

GOAL:
lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = 0

METHOD:

-/
theorem proof_gap_exercise_1015_1_7
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  (h7 : ¬ DifferentiableAt ℝ g 0)
  (h8 : exercise1015SameLimit (fun x : ℝ => (F x - F 0) / x) (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x))
  (h9 : exercise1015SameLimit (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x) (fun x : ℝ => |x|))
  (h10 : Tendsto (fun x : ℝ => |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  : Tendsto (fun x : ℝ => (F x - F 0) / x) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  sorry

/- Exercise 1015_1, gap 8
SHA-256: 237080fbd2269cf85542e0f9b0000f6822a7679bf1f37172d89e4ca09af213f8
PROOF GAP @8
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1
7. ¬DiffableFuncAt(g, 0)
8. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx))
9. lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx)) = lim_{ Δx → 0 } (|Δx|)
10. lim_{ Δx → 0 } (|Δx|) = 0
11. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = 0

GOAL:
DiffableFuncAt(F, 0)

METHOD:

-/
theorem proof_gap_exercise_1015_1_8
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  (h7 : ¬ DifferentiableAt ℝ g 0)
  (h8 : exercise1015SameLimit (fun x : ℝ => (F x - F 0) / x) (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x))
  (h9 : exercise1015SameLimit (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x) (fun x : ℝ => |x|))
  (h10 : Tendsto (fun x : ℝ => |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  (h11 : Tendsto (fun x : ℝ => (F x - F 0) / x) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  : DifferentiableAt ℝ F 0 := by
  sorry

/- Exercise 1015_1, gap 9
SHA-256: 80e98945aebdba0bf68ca2fd6d39b0661b23b77f9d7060008f1826bb07a6e85a
PROOF GAP @9
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1
7. ¬DiffableFuncAt(g, 0)
8. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx))
9. lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx)) = lim_{ Δx → 0 } (|Δx|)
10. lim_{ Δx → 0 } (|Δx|) = 0
11. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = 0
12. DiffableFuncAt(F, 0)

GOAL:
FunDeri(F, 1, 1)(0) = 0

METHOD:

-/
theorem proof_gap_exercise_1015_1_9
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  (h7 : ¬ DifferentiableAt ℝ g 0)
  (h8 : exercise1015SameLimit (fun x : ℝ => (F x - F 0) / x) (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x))
  (h9 : exercise1015SameLimit (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x) (fun x : ℝ => |x|))
  (h10 : Tendsto (fun x : ℝ => |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  (h11 : Tendsto (fun x : ℝ => (F x - F 0) / x) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  (h12 : DifferentiableAt ℝ F 0)
  : deriv F 0 = 0 := by
  sorry

/- Exercise 1015_1, gap 10
SHA-256: 3af5168502e615327466c28d87eeca7a1f8747e8a19bb132b95d5380a411ae05
PROOF GAP @10
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. g = (fun x [x ∈ RealSet] . |x|)
3. F = (fun x [x ∈ RealSet] . f(x) * g(x))
4. (fun x [x ∈ RealSet] . f(x) * g(x)) = (fun x [x ∈ RealSet] . x * |x|)
5. DiffableFuncAt(f, 0)
6. FunDeri(f, 1, 1)(0) = 1
7. ¬DiffableFuncAt(g, 0)
8. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx))
9. lim_{ Δx → 0 } (frac(Δx * |Δx| - 0 * |0|, Δx)) = lim_{ Δx → 0 } (|Δx|)
10. lim_{ Δx → 0 } (|Δx|) = 0
11. lim_{ Δx → 0 } (frac(F(Δx) - F(0), Δx)) = 0
12. DiffableFuncAt(F, 0)
13. FunDeri(F, 1, 1)(0) = 0

GOAL:
¬(forall (f) (g) (F) (x_{0}), f : RealSet → RealSet ∧ g : RealSet → RealSet ∧ F : RealSet → RealSet ∧ x_{0} ∈ RealSet ∧ (exists (`ϵ`), `ϵ` ∈ RealSet ∧ `ϵ` > 0 ∧ Dom(f) = (x_{0} - `ϵ`, x_{0} + `ϵ`) ∧ Dom(g) = (x_{0} - `ϵ`, x_{0} + `ϵ`)) ∧ DiffableFuncAt(f, x_{0}) ∧ ¬DiffableFuncAt(g, x_{0}) ∧ F = f * g ⇒ ¬DiffableFuncAt(F, x_{0}))

METHOD:

-/
theorem proof_gap_exercise_1015_1_10
  (f g F : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : g = (fun x : ℝ => |x|))
  (h3 : F = (fun x : ℝ => f x * g x))
  (h4 : (fun x : ℝ => f x * g x) = (fun x : ℝ => x * |x|))
  (h5 : DifferentiableAt ℝ f 0)
  (h6 : deriv f 0 = 1)
  (h7 : ¬ DifferentiableAt ℝ g 0)
  (h8 : exercise1015SameLimit (fun x : ℝ => (F x - F 0) / x) (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x))
  (h9 : exercise1015SameLimit (fun x : ℝ => (x * |x| - 0 * |(0 : ℝ)|) / x) (fun x : ℝ => |x|))
  (h10 : Tendsto (fun x : ℝ => |x|) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  (h11 : Tendsto (fun x : ℝ => (F x - F 0) / x) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  (h12 : DifferentiableAt ℝ F 0)
  (h13 : deriv F 0 = 0)
  : ¬ (∀ (f g F : ℝ → ℝ) (x₀ : ℝ),
    x₀ ∈ (Set.univ : Set ℝ) ∧
    (∃ ε : ℝ, ε ∈ (Set.univ : Set ℝ) ∧ ε > 0 ∧
      exercise1015Dom f = Set.Ioo (x₀ - ε) (x₀ + ε) ∧
      exercise1015Dom g = Set.Ioo (x₀ - ε) (x₀ + ε)) ∧
    DifferentiableAt ℝ f x₀ ∧ ¬ DifferentiableAt ℝ g x₀ ∧
    F = (fun x => f x * g x) → ¬ DifferentiableAt ℝ F x₀) := by
  sorry

