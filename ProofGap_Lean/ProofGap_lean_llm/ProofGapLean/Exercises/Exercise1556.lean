import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1556

noncomputable section

def transformed (C : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := C * (f x) ^ 2

def IsMaximizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x ≤ u x₀

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

def MaximizersOn (u : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {x | IsMaximizerOn u s x}

def MinimizersOn (u : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {x | IsMinimizerOn u s x}

theorem gap1 (C : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    transformed C f x = C * (f x) ^ 2 := by
  rfl

theorem gap2 (C u v : ℝ) (hC : 0 < C) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : C * u ^ 2 ≤ C * v ^ 2) :
    u ≤ v := by
  have hs : u ^ 2 ≤ v ^ 2 := le_of_mul_le_mul_left h hC
  nlinarith

theorem gap3 (C : ℝ) (f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hC : 0 < C) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hmax : IsMaximizerOn (transformed C f) s x₀) :
    IsMaximizerOn f s x₀ := by
  rcases hmax with ⟨hx₀, hbound⟩
  refine ⟨hx₀, ?_⟩
  intro x hx
  apply gap2 C (f x) (f x₀) hC (hf x hx) (hf x₀ hx₀)
  simpa only [transformed] using hbound x hx

theorem gap4 (C : ℝ) (f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hC : 0 < C) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hmax : IsMaximizerOn f s x₀) :
    IsMaximizerOn (transformed C f) s x₀ := by
  rcases hmax with ⟨hx₀, hbound⟩
  refine ⟨hx₀, ?_⟩
  intro x hx
  simp only [transformed]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
  have hfx : 0 ≤ f x := hf x hx
  have hfx₀ : 0 ≤ f x₀ := hf x₀ hx₀
  have hle : f x ≤ f x₀ := hbound x hx
  nlinarith

theorem gap5 (C : ℝ) (f : ℝ → ℝ) (s : Set ℝ)
    (hC : 0 < C) (hf : ∀ x ∈ s, 0 ≤ f x) :
    MaximizersOn (transformed C f) s = MaximizersOn f s := by
  apply Set.ext
  intro x
  change IsMaximizerOn (transformed C f) s x ↔ IsMaximizerOn f s x
  constructor
  · exact gap3 C f s x hC hf
  · exact gap4 C f s x hC hf

theorem gap6 (C u v : ℝ) (hC : 0 < C) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : C * u ^ 2 ≤ C * v ^ 2) :
    u ≤ v := by
  exact gap2 C u v hC hu hv h

theorem gap7 (C : ℝ) (f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hC : 0 < C) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hmin : IsMinimizerOn (transformed C f) s x₀) :
    IsMinimizerOn f s x₀ := by
  rcases hmin with ⟨hx₀, hbound⟩
  refine ⟨hx₀, ?_⟩
  intro x hx
  apply gap6 C (f x₀) (f x) hC (hf x₀ hx₀) (hf x hx)
  simpa only [transformed] using hbound x hx

theorem gap8 (C : ℝ) (f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ)
    (hC : 0 < C) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hmin : IsMinimizerOn f s x₀) :
    IsMinimizerOn (transformed C f) s x₀ := by
  rcases hmin with ⟨hx₀, hbound⟩
  refine ⟨hx₀, ?_⟩
  intro x hx
  simp only [transformed]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
  have hfx₀ : 0 ≤ f x₀ := hf x₀ hx₀
  have hfx : 0 ≤ f x := hf x hx
  have hle : f x₀ ≤ f x := hbound x hx
  nlinarith

theorem gap9 (C : ℝ) (f : ℝ → ℝ) (s : Set ℝ)
    (hC : 0 < C) (hf : ∀ x ∈ s, 0 ≤ f x) :
    MinimizersOn (transformed C f) s = MinimizersOn f s := by
  apply Set.ext
  intro x
  change IsMinimizerOn (transformed C f) s x ↔ IsMinimizerOn f s x
  constructor
  · exact gap7 C f s x hC hf
  · exact gap8 C f s x hC hf

theorem gap10 (C : ℝ) (f : ℝ → ℝ) (s : Set ℝ)
    (hC : 0 < C) (hf : ∀ x ∈ s, 0 ≤ f x) :
    MaximizersOn (transformed C f) s = MaximizersOn f s ∧
      MinimizersOn (transformed C f) s = MinimizersOn f s := by
  exact ⟨gap5 C f s hC hf, gap9 C f s hC hf⟩

end

end ProofGap.Exercise1556
