import Mathlib

open scoped BigOperators Topology
open Filter

namespace Exercise2219

-- Natural indices enumerate the positive integers cofinally; n = 0 is irrelevant
-- to atTop. Ico a n equals the source inclusive range a,...,n-1 for n > 0.
noncomputable def originalSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 n, (i : ℝ) / (n : ℝ) ^ 2

noncomputable def leftSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 0 n, ((i : ℝ) / (n : ℝ)) * (1 / (n : ℝ))

-- Equality of the two existing finite limits, with the same witness.
def EqualLimits : Prop :=
  ∃ L : ℝ, Tendsto originalSum atTop (𝓝 L) ∧ Tendsto leftSum atTop (𝓝 L)

-- Thms 267-268: continuity at every point of the indicated set.
def ContinuousOnSource (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1, ContinuousAt f x

-- The original dx is the differential of the identity: its coefficient is 1.
noncomputable def identityIntegral : ℝ := ∫ x in (0 : ℝ)..1, x

end Exercise2219

open Exercise2219

/- Exercise 2219, gap 1
PROOF GAP @1
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)

GOAL:
ContinuousFuncOn(f, [0, 1])

METHOD:
-/
theorem proof_gap_exercise_2219_1
  (f : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  : ContinuousOnSource f := by
  sorry

/- Exercise 2219, gap 2
PROOF GAP @2
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. ContinuousFuncOn(f, [0, 1])

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n - 1 } (frac(i, n^{2}))) = lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (frac(i, n) * frac(1, n)))

METHOD:
-/
theorem proof_gap_exercise_2219_2
  (f : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : ContinuousOnSource f)
  : EqualLimits := by
  sorry

/- Exercise 2219, gap 3
PROOF GAP @3
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. ContinuousFuncOn(f, [0, 1])
3. lim_{ n → +∞ } (sum_{ i = 1 }^{ n - 1 } (frac(i, n^{2}))) = lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (frac(i, n) * frac(1, n)))

GOAL:
lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (frac(i, n) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . x) * diff(fun x [x ∈ RealSet] . x))

METHOD:
-/
theorem proof_gap_exercise_2219_3
  (f : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : ContinuousOnSource f)
  (h3 : EqualLimits)
  : Tendsto leftSum atTop (𝓝 identityIntegral) := by
  sorry

/- Exercise 2219, gap 4
PROOF GAP @4
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. ContinuousFuncOn(f, [0, 1])
3. lim_{ n → +∞ } (sum_{ i = 1 }^{ n - 1 } (frac(i, n^{2}))) = lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (frac(i, n) * frac(1, n)))
4. lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (frac(i, n) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . x) * diff(fun x [x ∈ RealSet] . x))

GOAL:
DefInt(0, 1, (fun x [x ∈ RealSet] . x) * diff(fun x [x ∈ RealSet] . x)) = frac(1, 2)

METHOD:
-/
theorem proof_gap_exercise_2219_4
  (f : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : ContinuousOnSource f)
  (h3 : EqualLimits)
  (h4 : Tendsto leftSum atTop (𝓝 identityIntegral))
  : identityIntegral = (1 : ℝ) / 2 := by
  sorry

/- Exercise 2219, gap 5
PROOF GAP @5
ASSUM:
1. f = (fun x [x ∈ RealSet] . x)
2. ContinuousFuncOn(f, [0, 1])
3. lim_{ n → +∞ } (sum_{ i = 1 }^{ n - 1 } (frac(i, n^{2}))) = lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (frac(i, n) * frac(1, n)))
4. lim_{ n → +∞ } (sum_{ i = 0 }^{ n - 1 } (frac(i, n) * frac(1, n))) = DefInt(0, 1, (fun x [x ∈ RealSet] . x) * diff(fun x [x ∈ RealSet] . x))
5. DefInt(0, 1, (fun x [x ∈ RealSet] . x) * diff(fun x [x ∈ RealSet] . x)) = frac(1, 2)

GOAL:
lim_{ n → +∞ } (sum_{ i = 1 }^{ n - 1 } (frac(i, n^{2}))) = frac(1, 2)

METHOD:
-/
theorem proof_gap_exercise_2219_5
  (f : ℝ → ℝ)
  (h1 : f = (fun x : ℝ => x))
  (h2 : ContinuousOnSource f)
  (h3 : EqualLimits)
  (h4 : Tendsto leftSum atTop (𝓝 identityIntegral))
  (h5 : identityIntegral = (1 : ℝ) / 2)
  : Tendsto originalSum atTop (𝓝 ((1 : ℝ) / 2)) := by
  sorry

