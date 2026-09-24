import Mathlib

open scoped BigOperators Topology
open Filter

namespace Exercise2223

-- Natural indices agree with the original positive integer indices on the tail n ≥ 1.
-- The additional value at n = 0 has no effect on a limit atTop.
noncomputable def powerSum (p : ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc (1 : ℕ) n, Real.rpow (i : ℝ) p) /
    Real.rpow (n : ℝ) (p + 1)

noncomputable def riemannSum (p : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (1 : ℕ) n,
    Real.rpow ((i : ℝ) / (n : ℝ)) p * (1 / (n : ℝ))

-- Equality of the two existing finite limits.
def sameLimit (p : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (powerSum p) atTop (𝓝 L) ∧
    Tendsto (riemannSum p) atTop (𝓝 L)

-- diff(id) is dx, so the integral is the ordinary oriented interval integral.
noncomputable def powerIntegral (p : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(1 : ℝ), Real.rpow x p

end Exercise2223

open Exercise2223

/- Exercise 2223, gap 1
SHA-256: f375843dcdce4f5d968477e3772851e5aff3c8e73db893b740c6f97f8238afe0
PROOF GAP @1
ASSUM:
1. p ∈ RealSet
2. p > 0

GOAL:
lim_{ n → +∞ } (frac(sum_{ i = 1 }^{ n } (i^{p}), n^{p + 1})) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(i, n)^{p} * frac(1, n)))

METHOD:

-/
theorem proof_gap_exercise_2223_1
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 0)
  : sameLimit p := by
  sorry

/- Exercise 2223, gap 2
SHA-256: 0b5cbdf42fcf8294ad45d6a2a6b384f5a0ce6c5c18602aa1b10b85ea4160716a
PROOF GAP @2
ASSUM:
1. p ∈ RealSet
2. p > 0
3. lim_{ n → +∞ } (frac(sum_{ i = 1 }^{ n } (i^{p}), n^{p + 1})) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(i, n)^{p} * frac(1, n)))

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(i, n)^{p} * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . x^{p}) * diff(fun x [x ∈ RealSet] . x))

METHOD:

-/
theorem proof_gap_exercise_2223_2
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 0)
  (h3 : sameLimit p)
  : Tendsto (riemannSum p) atTop (𝓝 (powerIntegral p)) := by
  sorry

/- Exercise 2223, gap 3
SHA-256: 32f7c4cf0efc1809ac8072b53b8d502a7da2066ef3375c47ebf0b2e3cadf0131
PROOF GAP @3
ASSUM:
1. p ∈ RealSet
2. p > 0
3. lim_{ n → +∞ } (frac(sum_{ i = 1 }^{ n } (i^{p}), n^{p + 1})) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(i, n)^{p} * frac(1, n)))
4. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(i, n)^{p} * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . x^{p}) * diff(fun x [x ∈ RealSet] . x))

GOAL:
DefInt(0, 1, (fun x [x ∈ RealSet] . x^{p}) * diff(fun x [x ∈ RealSet] . x)) = frac(1, p + 1)

METHOD:

-/
theorem proof_gap_exercise_2223_3
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 0)
  (h3 : sameLimit p)
  (h4 : Tendsto (riemannSum p) atTop (𝓝 (powerIntegral p)))
  : powerIntegral p = 1 / (p + 1) := by
  sorry

/- Exercise 2223, gap 4
SHA-256: 2bb3247aec9ae8ad8f508c711be0f47be98a2efce07587ed34b0f80d0e037d8b
PROOF GAP @4
ASSUM:
1. p ∈ RealSet
2. p > 0
3. lim_{ n → +∞ } (frac(sum_{ i = 1 }^{ n } (i^{p}), n^{p + 1})) = lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(i, n)^{p} * frac(1, n)))
4. lim_{ n → +∞ } (sum_{ i = 1 }^{ n } (frac(i, n)^{p} * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . x^{p}) * diff(fun x [x ∈ RealSet] . x))
5. DefInt(0, 1, (fun x [x ∈ RealSet] . x^{p}) * diff(fun x [x ∈ RealSet] . x)) = frac(1, p + 1)

GOAL:
lim_{ n → +∞ } (frac(sum_{ i = 1 }^{ n } (i^{p}), n^{p + 1})) = frac(1, p + 1)

METHOD:

-/
theorem proof_gap_exercise_2223_4
  (p : ℝ)
  (h1 : p ∈ (Set.univ : Set ℝ))
  (h2 : p > 0)
  (h3 : sameLimit p)
  (h4 : Tendsto (riemannSum p) atTop (𝓝 (powerIntegral p)))
  (h5 : powerIntegral p = 1 / (p + 1))
  : Tendsto (powerSum p) atTop (𝓝 (1 / (p + 1))) := by
  sorry

