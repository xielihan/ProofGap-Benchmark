import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise791

noncomputable section

/-- Source: `proof_gap/exercise_791/1.txt`; remove the shadowed existential `a`. -/
theorem gap1 (f : ℝ → ℝ) (a A : ℝ)
    (hlim : Filter.Tendsto f Filter.atTop (nhds A)) :
    ∀ ε > 0, ∃ X > a, ∀ x₁ > X, ∀ x₂ > X, |f x₁ - f x₂| < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hevent : ∀ᶠ x in Filter.atTop, f x ∈ Metric.ball A (ε / 2) :=
    hlim.eventually (Metric.ball_mem_nhds A hε2)
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max a b + 1, by linarith [le_max_left a b], ?_⟩
  intro x₁ hx₁ x₂ hx₂
  have hbx₁ : b ≤ x₁ := by linarith [le_max_right a b]
  have hbx₂ : b ≤ x₂ := by linarith [le_max_right a b]
  have hf₁ : dist (f x₁) A < ε / 2 := by
    simpa only [Metric.mem_ball] using hb x₁ hbx₁
  have hf₂ : dist (f x₂) A < ε / 2 := by
    simpa only [Metric.mem_ball] using hb x₂ hbx₂
  have hf₂' : dist A (f x₂) < ε / 2 := by
    rw [dist_comm]
    exact hf₂
  rw [← Real.dist_eq]
  calc
    dist (f x₁) (f x₂) ≤ dist (f x₁) A + dist A (f x₂) := dist_triangle _ _ _
    _ < ε := by linarith

/-- Source: `proof_gap/exercise_791/2.txt`; bind `ε` outside the irrelevant existence of `X`. -/
theorem gap2 (f : ℝ → ℝ) (a X : ℝ) (hcont : ContinuousOn f (Set.Ici a)) :
    ContinuousOn f (Set.Icc a (X + 1)) := by
  exact hcont.mono (by
    intro x hx
    exact hx.1)

/-- Source: `proof_gap/exercise_791/3.txt`; remove shadowed `a, X`. -/
theorem gap3 (f : ℝ → ℝ) (a X : ℝ)
    (hcont : ContinuousOn f (Set.Icc a (X + 1))) :
    ∀ ε > 0, ∃ δ' > 0, ∀ x₁ ∈ Set.Icc a (X + 1),
      ∀ x₂ ∈ Set.Icc a (X + 1),
        |x₁ - x₂| < δ' → |f x₁ - f x₂| < ε := by
  have hK : IsCompact (Set.Icc a (X + 1)) := isCompact_Icc
  have hu : UniformContinuousOn f (Set.Icc a (X + 1)) :=
    hK.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hu
  simpa only [Real.dist_eq] using hu

/-- Source: `proof_gap/exercise_791/4.txt`; choose a small δ to bridge the compact and tail regions. -/
theorem gap4 (a X δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ x₁ ∈ Set.Ici a, ∀ x₂ ∈ Set.Ici a, |x₁ - x₂| < δ →
      (x₁ ∈ Set.Icc a (X + 1) ∧ x₂ ∈ Set.Icc a (X + 1)) ∨
      (x₁ > X ∧ x₂ > X) := by
  intro x₁ hx₁ x₂ hx₂ hclose
  rcases abs_lt.mp hclose with ⟨hclose₁, hclose₂⟩
  by_cases hx₁X : x₁ ≤ X
  · left
    constructor
    · exact ⟨hx₁, by linarith⟩
    · exact ⟨hx₂, by linarith⟩
  · have hx₁tail : X < x₁ := lt_of_not_ge hx₁X
    by_cases hx₂X : x₂ ≤ X
    · left
      constructor
      · exact ⟨hx₁, by linarith⟩
      · exact ⟨hx₂, by linarith⟩
    · right
      exact ⟨hx₁tail, lt_of_not_ge hx₂X⟩

/-- Source: `proof_gap/exercise_791/5.txt`; move `δ` under `ε`. -/
theorem gap5 (f : ℝ → ℝ) (a : ℝ)
    (hlocal : ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Ici a, ∀ x₂ ∈ Set.Ici a,
      |x₁ - x₂| < δ → |f x₁ - f x₂| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Ici a, ∀ x₂ ∈ Set.Ici a,
      |x₁ - x₂| < δ → |f x₁ - f x₂| < ε := by
  exact hlocal

/-- Source: `proof_gap/exercise_791/6.txt`. -/
theorem gap6 (f : ℝ → ℝ) (a : ℝ)
    (hε : ∀ ε > 0, ∃ δ > 0, ∀ x₁ ∈ Set.Ici a, ∀ x₂ ∈ Set.Ici a,
      |x₁ - x₂| < δ → |f x₁ - f x₂| < ε) :
    UniformContinuousOn f (Set.Ici a) := by
  rw [Metric.uniformContinuousOn_iff]
  simpa only [Real.dist_eq] using hε

/-- Source: `proof_gap/exercise_791/7.txt`. -/
theorem gap7 (f : ℝ → ℝ) (a : ℝ)
    (hcont : ContinuousOn f (Set.Ici a))
    (hlim : ∃ A, Filter.Tendsto f Filter.atTop (nhds A)) :
    UniformContinuousOn f (Set.Ici a) := by
  rcases hlim with ⟨A, hA⟩
  apply gap6 f a
  intro ε hε
  obtain ⟨X, hXa, htail⟩ := gap1 f a A hA ε hε
  have hcompactCont : ContinuousOn f (Set.Icc a (X + 1)) :=
    gap2 f a X hcont
  obtain ⟨δ', hδ', hcompact⟩ :=
    gap3 f a X hcompactCont ε hε
  have hδ : 0 < min δ' 1 := lt_min hδ' zero_lt_one
  refine ⟨min δ' 1, hδ, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hclose
  have hregions :=
    gap4 a X (min δ' 1) hδ (min_le_right δ' 1)
      x₁ hx₁ x₂ hx₂ hclose
  rcases hregions with hcompactRegion | htailRegion
  · exact hcompact x₁ hcompactRegion.1 x₂ hcompactRegion.2
      (lt_of_lt_of_le hclose (min_le_left δ' 1))
  · exact htail x₁ htailRegion.1 x₂ htailRegion.2

end

end ProofGap.Exercise791
