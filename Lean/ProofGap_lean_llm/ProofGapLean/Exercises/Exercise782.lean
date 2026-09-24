import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise782

def ParametrizesFunction (φ ψ : ℝ → ℝ) : Prop :=
  ∃ y : ℝ → ℝ, ∀ t, y (φ t) = ψ t

def FiberConsistent (φ ψ : ℝ → ℝ) : Prop :=
  ∀ t₁ t₂, φ t₁ = φ t₂ → ψ t₁ = ψ t₂

theorem gap1 (φ ψ : ℝ → ℝ) (h : ¬ FiberConsistent φ ψ) :
    ∃ x₀ t₁ t₂, φ t₁ = x₀ ∧ φ t₂ = x₀ ∧ t₁ ≠ t₂ ∧ ψ t₁ ≠ ψ t₂ := by
  by_contra hn
  apply h
  intro t₁ t₂ hφ
  by_contra hψ
  apply hn
  refine ⟨φ t₁, t₁, t₂, rfl, hφ.symm, ?_, hψ⟩
  intro ht
  apply hψ
  rw [ht]
theorem gap2 (φ ψ : ℝ → ℝ) (h : ¬ FiberConsistent φ ψ) :
    ∃ t₁ t₂, φ t₁ = φ t₂ ∧ ψ t₁ ≠ ψ t₂ := by
  by_contra hn
  apply h
  intro t₁ t₂ hφ
  by_contra hψ
  apply hn
  exact ⟨t₁, t₂, hφ, hψ⟩
theorem gap3 (φ ψ : ℝ → ℝ) (h : ¬ FiberConsistent φ ψ) :
    ¬ ParametrizesFunction φ ψ := by
  intro hp
  obtain ⟨y, hy⟩ := hp
  obtain ⟨t₁, t₂, hφ, hψ⟩ := gap2 φ ψ h
  apply hψ
  calc
    ψ t₁ = y (φ t₁) := (hy t₁).symm
    _ = y (φ t₂) := congrArg y hφ
    _ = ψ t₂ := hy t₂
theorem gap4 (φ ψ : ℝ → ℝ) (hy : ParametrizesFunction φ ψ)
    (h : ¬ FiberConsistent φ ψ) : False := by
  exact gap3 φ ψ h hy
theorem gap5 (φ ψ : ℝ → ℝ) (hy : ParametrizesFunction φ ψ) :
    FiberConsistent φ ψ := by
  obtain ⟨y, hy⟩ := hy
  intro t₁ t₂ hφ
  calc
    ψ t₁ = y (φ t₁) := (hy t₁).symm
    _ = y (φ t₂) := congrArg y hφ
    _ = ψ t₂ := hy t₂
theorem gap6 (φ ψ : ℝ → ℝ) :
    ParametrizesFunction φ ψ → FiberConsistent φ ψ := by
  intro hy
  exact gap5 φ ψ hy
theorem gap7 (φ ψ : ℝ → ℝ) (h : FiberConsistent φ ψ) :
    ∃ y : ℝ → ℝ, ∀ x₀ ∈ Set.range φ, ∃ t₀, φ t₀ = x₀ ∧ ψ t₀ = y x₀ := by
  classical
  let y : ℝ → ℝ := fun x =>
    if hx : x ∈ Set.range φ then ψ (Classical.choose hx) else 0
  refine ⟨y, ?_⟩
  intro x₀ hx
  refine ⟨Classical.choose hx, Classical.choose_spec hx, ?_⟩
  simp only [y, dif_pos hx]
theorem gap8 (φ ψ : ℝ → ℝ) (h : FiberConsistent φ ψ) :
    ∀ x₀ ∈ Set.range φ, ∀ t₁ t₂, φ t₁ = x₀ → φ t₂ = x₀ → ψ t₁ = ψ t₂ := by
  intro x₀ hx t₁ t₂ ht₁ ht₂
  apply h
  exact ht₁.trans ht₂.symm
theorem gap9 (φ ψ : ℝ → ℝ) :
    FiberConsistent φ ψ → ParametrizesFunction φ ψ := by
  classical
  intro h
  let y : ℝ → ℝ := fun x =>
    if hx : x ∈ Set.range φ then ψ (Classical.choose hx) else 0
  refine ⟨y, ?_⟩
  intro t
  have hr : φ t ∈ Set.range φ := ⟨t, rfl⟩
  simp only [y, dif_pos hr]
  apply h
  exact Classical.choose_spec hr
theorem gap10 (φ ψ : ℝ → ℝ) :
    FiberConsistent φ ψ → ParametrizesFunction φ ψ := by
  exact gap9 φ ψ
theorem gap11 (φ ψ : ℝ → ℝ) :
    ParametrizesFunction φ ψ ↔ FiberConsistent φ ψ := by
  constructor
  · exact gap6 φ ψ
  · exact gap10 φ ψ

end ProofGap.Exercise782
