import Mathlib

open scoped Topology
open Filter

namespace Exercise796

-- Graphs preserve domains in the source's set-theoretic function equalities.
def graph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | p.2 = f p.1}

def intervalGraph (F : Set.Icc (0 : ℝ) Real.pi → ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ h : p.1 ∈ Set.Icc (0 : ℝ) Real.pi, p.2 = F ⟨p.1, h⟩}

def restrictGraph (G : Set (ℝ × ℝ)) (S : Set ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ G ∧ p.1 ∈ S}

-- No otherwise branch is present in the source: do not invent outside values.
def casesGraph : Set (ℝ × ℝ) :=
  {p | (p.1 = 0 ∧ p.2 = 1) ∨
    (0 < p.1 ∧ p.1 < Real.pi ∧ p.2 = Real.sin p.1 / p.1) ∨
    (p.1 = Real.pi ∧ p.2 = 0)}

-- Thms 267 and 268 use continuity at each point in the function's domain.
def continuousFuncOn (F : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ContinuousAt F x

end Exercise796

open Exercise796

/- Exercise 796, gap 1
PROOF GAP @1
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(0, π) ⇒ f(x) = frac(sin(x), x)

GOAL:
lim_{ x → 0^+ } (frac(sin(x), x)) = 1

METHOD:

-/
theorem proof_gap_exercise_796_1
  (f : ℝ → ℝ)
  (F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ioo (0 : ℝ) Real.pi →
    f x = Real.sin x / x)
  : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  sorry

/- Exercise 796, gap 2
PROOF GAP @2
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(0, π) ⇒ f(x) = frac(sin(x), x)
4. lim_{ x → 0^+ } (frac(sin(x), x)) = 1
5. F = (fun x [x ∈ RealSet] . cases{ 1 if x = 0; frac(sin(x), x) if 0 < x ∧ x < π; 0 if x = π })

GOAL:
ContinuousFuncOn(F, [0, π])

METHOD:

-/
theorem proof_gap_exercise_796_2
  (f : ℝ → ℝ)
  (F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ioo (0 : ℝ) Real.pi →
    f x = Real.sin x / x)
  (h4 : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (h5 : graph F = casesGraph)
  : continuousFuncOn F (Set.Icc (0 : ℝ) Real.pi) := by
  sorry

/- Exercise 796, gap 3
PROOF GAP @3
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(0, π) ⇒ f(x) = frac(sin(x), x)
4. lim_{ x → 0^+ } (frac(sin(x), x)) = 1
5. F = (fun x [x ∈ RealSet] . cases{ 1 if x = 0; frac(sin(x), x) if 0 < x ∧ x < π; 0 if x = π })
6. ContinuousFuncOn(F, [0, π])

GOAL:
UniformContinuousFuncOn(F, [0, π])

METHOD:
[@method 根据 "康托尔定理" @]
-/
theorem proof_gap_exercise_796_3
  (f : ℝ → ℝ)
  (F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ioo (0 : ℝ) Real.pi →
    f x = Real.sin x / x)
  (h4 : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (h5 : graph F = casesGraph)
  (h6 : continuousFuncOn F (Set.Icc (0 : ℝ) Real.pi))
  : UniformContinuousOn F (Set.Icc (0 : ℝ) Real.pi) := by
  sorry

/- Exercise 796, gap 4
PROOF GAP @4
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(0, π) ⇒ f(x) = frac(sin(x), x)
4. lim_{ x → 0^+ } (frac(sin(x), x)) = 1
5. F = (fun x [x ∈ RealSet] . cases{ 1 if x = 0; frac(sin(x), x) if 0 < x ∧ x < π; 0 if x = π })
6. ContinuousFuncOn(F, [0, π])
7. UniformContinuousFuncOn(F, [0, π])

GOAL:
RestrictFunc(F, IntervalLoRo(0, π)) = f

METHOD:

-/
theorem proof_gap_exercise_796_4
  (f : ℝ → ℝ)
  (F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ioo (0 : ℝ) Real.pi →
    f x = Real.sin x / x)
  (h4 : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (h5 : graph F = casesGraph)
  (h6 : continuousFuncOn F (Set.Icc (0 : ℝ) Real.pi))
  (h7 : UniformContinuousOn F (Set.Icc (0 : ℝ) Real.pi))
  : restrictGraph (graph F) (Set.Ioo (0 : ℝ) Real.pi) = graph f := by
  sorry

/- Exercise 796, gap 5
PROOF GAP @5
ASSUM:
1. f : RealSet → RealSet
2. F : [0, π] → RealSet
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(0, π) ⇒ f(x) = frac(sin(x), x)
4. lim_{ x → 0^+ } (frac(sin(x), x)) = 1
5. F = (fun x [x ∈ [0, π]] . cases{ 1 if x = 0; frac(sin(x), x) if 0 < x ∧ x < π; 0 if x = π })
6. ContinuousFuncOn(F, [0, π])
7. UniformContinuousFuncOn(F, [0, π])
8. RestrictFunc(F, IntervalLoRo(0, π)) = f
GOAL:
UniformContinuousFuncOn(f, IntervalLoRo(0, π))

METHOD:

-/
theorem proof_gap_exercise_796_5
  (f : ℝ → ℝ)
  (F : Set.Icc (0 : ℝ) Real.pi → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ioo (0 : ℝ) Real.pi →
    f x = Real.sin x / x)
  (h4 : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (h5 : intervalGraph F = casesGraph)
  (h6 : Continuous F)
  (h7 : UniformContinuous F)
  (h8 : restrictGraph (intervalGraph F) (Set.Ioo (0 : ℝ) Real.pi) = graph f)
  : UniformContinuousOn f (Set.Ioo (0 : ℝ) Real.pi) := by
  sorry

/- Exercise 796, gap 6
PROOF GAP @6
ASSUM:
1. f : RealSet → RealSet
2. F : RealSet → RealSet
3. forall (x), x ∈ RealSet ∧ x ∈ IntervalLoRo(0, π) ⇒ f(x) = frac(sin(x), x)
4. lim_{ x → 0^+ } (frac(sin(x), x)) = 1
5. F = (fun x [x ∈ RealSet] . cases{ 1 if x = 0; frac(sin(x), x) if 0 < x ∧ x < π; 0 if x = π })
6. ContinuousFuncOn(F, [0, π])
7. UniformContinuousFuncOn(F, [0, π])
8. RestrictFunc(F, IntervalLoRo(0, π)) = f
9. UniformContinuousFuncOn(f, IntervalLoRo(0, π))

GOAL:
UniformContinuousFuncOn(f, IntervalLoRo(0, π))

METHOD:

-/
theorem proof_gap_exercise_796_6
  (f : ℝ → ℝ)
  (F : ℝ → ℝ)
  (h3 : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x ∈ Set.Ioo (0 : ℝ) Real.pi →
    f x = Real.sin x / x)
  (h4 : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)))
  (h5 : graph F = casesGraph)
  (h6 : continuousFuncOn F (Set.Icc (0 : ℝ) Real.pi))
  (h7 : UniformContinuousOn F (Set.Icc (0 : ℝ) Real.pi))
  (h8 : restrictGraph (graph F) (Set.Ioo (0 : ℝ) Real.pi) = graph f)
  (h9 : UniformContinuousOn f (Set.Ioo (0 : ℝ) Real.pi))
  : UniformContinuousOn f (Set.Ioo (0 : ℝ) Real.pi) := by
  sorry

