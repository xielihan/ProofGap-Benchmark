import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3751

noncomputable section

open Filter
open scoped Interval Topology

def tailPartial (f : ℝ → ℝ → ℝ) (b y A : ℝ) : ℝ :=
  ∫ x in b..A, f x y

def TailLimit (f : ℝ → ℝ → ℝ) (b y L : ℝ) : Prop :=
  Tendsto (tailPartial f b y) atTop (𝓝 L)

def UniformTailSmall (f : ℝ → ℝ → ℝ) (y₁ y₂ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, ∀ b : ℝ, B ≤ b →
      ∀ y ∈ Set.Ioo y₁ y₂, ∀ L : ℝ,
        TailLimit f b y L → |L| < ε

def NonUniformWitness (f : ℝ → ℝ → ℝ) (y₁ y₂ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ B : ℝ, ∃ b : ℝ, B ≤ b ∧
      ∃ y ∈ Set.Ioo y₁ y₂, ∃ L : ℝ,
        TailLimit f b y L ∧ ε₀ ≤ |L|

theorem gap1 (f : ℝ → ℝ → ℝ) (y₁ y₂ : ℝ) :
    ¬ UniformTailSmall f y₁ y₂ ↔
      NonUniformWitness f y₁ y₂ := by
  classical
  constructor
  · intro hNotUniform
    unfold NonUniformWitness
    by_contra hNoWitness
    apply hNotUniform
    unfold UniformTailSmall
    intro ε hε
    by_contra hNoB
    apply hNoWitness
    refine ⟨ε, hε, ?_⟩
    intro B
    by_contra hNoCounter
    apply hNoB
    refine ⟨B, ?_⟩
    intro b hBb y hy L hTail
    by_contra hNotLt
    apply hNoCounter
    refine ⟨b, hBb, y, hy, L, hTail, ?_⟩
    exact le_of_not_gt hNotLt
  · intro hWitness hUniform
    unfold NonUniformWitness at hWitness
    unfold UniformTailSmall at hUniform
    rcases hWitness with ⟨ε, hε, hbad⟩
    rcases hUniform ε hε with ⟨B, hB⟩
    rcases hbad B with ⟨b, hBb, y, hy, L, hTail, hLower⟩
    exact (not_lt_of_ge hLower) (hB b hBb y hy L hTail)

theorem gap2 (f : ℝ → ℝ → ℝ) (y₁ y₂ : ℝ) :
    UniformTailSmall f y₁ y₂ ↔
      ¬ NonUniformWitness f y₁ y₂ := by
  constructor
  · intro hUniform hWitness
    exact (gap1 f y₁ y₂).mpr hWitness hUniform
  · intro hNoWitness
    by_contra hNotUniform
    exact hNoWitness ((gap1 f y₁ y₂).mp hNotUniform)

end

end ProofGap.Exercise3751
