import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise1557

noncomputable section

def IsMaximizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x ≤ u x₀

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

def MaximizersOn (u : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {x | IsMaximizerOn u s x}

def MinimizersOn (u : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {x | IsMinimizerOn u s x}

theorem gap1 (φ f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hφ : StrictMono φ) (hmax : IsMaximizerOn f s x₀) :
    ∀ x ∈ s, φ (f x) ≤ φ (f x₀) := by
  intro x hx
  exact hφ.monotone (hmax.2 x hx)

theorem gap2 (φ f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hφ : StrictMono φ) (hmax : IsMaximizerOn f s x₀) :
    IsMaximizerOn (φ ∘ f) s x₀ := by
  constructor
  · exact hmax.1
  · intro x hx
    change φ (f x) ≤ φ (f x₀)
    exact gap1 φ f s x₀ hφ hmax x hx

theorem gap3 (φ f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hφ : StrictMono φ) (hmax : IsMaximizerOn (φ ∘ f) s x₀) :
    IsMaximizerOn f s x₀ := by
  constructor
  · exact hmax.1
  · intro x hx
    have hcomp := hmax.2 x hx
    change φ (f x) ≤ φ (f x₀) at hcomp
    apply le_of_not_gt
    intro hcontra
    exact (not_lt_of_ge hcomp) (hφ hcontra)

theorem gap4 (φ f : ℝ → ℝ) (s : Set ℝ) (hφ : StrictMono φ) :
    MaximizersOn f s = MaximizersOn (φ ∘ f) s := by
  ext x
  constructor
  · intro hx
    change IsMaximizerOn f s x at hx
    change IsMaximizerOn (φ ∘ f) s x
    exact gap2 φ f s x hφ hx
  · intro hx
    change IsMaximizerOn (φ ∘ f) s x at hx
    change IsMaximizerOn f s x
    exact gap3 φ f s x hφ hx

theorem gap5 (φ f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hφ : StrictMono φ) (hmin : IsMinimizerOn f s x₀) :
    ∀ x ∈ s, φ (f x₀) ≤ φ (f x) := by
  intro x hx
  exact hφ.monotone (hmin.2 x hx)

theorem gap6 (φ f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hφ : StrictMono φ) (hmin : IsMinimizerOn f s x₀) :
    IsMinimizerOn (φ ∘ f) s x₀ := by
  constructor
  · exact hmin.1
  · intro x hx
    change φ (f x₀) ≤ φ (f x)
    exact gap5 φ f s x₀ hφ hmin x hx

theorem gap7 (φ f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hφ : StrictMono φ) (hmin : IsMinimizerOn (φ ∘ f) s x₀) :
    IsMinimizerOn f s x₀ := by
  constructor
  · exact hmin.1
  · intro x hx
    have hcomp := hmin.2 x hx
    change φ (f x₀) ≤ φ (f x) at hcomp
    apply le_of_not_gt
    intro hcontra
    exact (not_lt_of_ge hcomp) (hφ hcontra)

theorem gap8 (φ f : ℝ → ℝ) (s : Set ℝ) (hφ : StrictMono φ) :
    MaximizersOn f s = MaximizersOn (φ ∘ f) s ∧
      MinimizersOn f s = MinimizersOn (φ ∘ f) s := by
  constructor
  · exact gap4 φ f s hφ
  · ext x
    constructor
    · intro hx
      change IsMinimizerOn f s x at hx
      change IsMinimizerOn (φ ∘ f) s x
      exact gap6 φ f s x hφ hx
    · intro hx
      change IsMinimizerOn (φ ∘ f) s x at hx
      change IsMinimizerOn f s x
      exact gap7 φ f s x hφ hx

end

end ProofGap.Exercise1557
