import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise3209

noncomputable section

open scoped Topology

def rectangle (a A b B : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo a A ×ˢ Set.Ioo b B

def jointFunction (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f p.1 p.2

def F (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x (φ x)

theorem gap1 (f : ℝ → ℝ → ℝ) (a A b B : ℝ)
    (hf : ContinuousOn (jointFunction f) (rectangle a A b B)) :
    ∀ x₀ y₀ : ℝ, (x₀, y₀) ∈ rectangle a A b B →
      ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ,
        (x, y) ∈ rectangle a A b B →
        |x - x₀| < δ → |y - y₀| < δ →
          |f x y - f x₀ y₀| < ε := by
  intro x₀ y₀ hxy₀ ε hε
  rcases (Metric.continuousWithinAt_iff.mp
      (hf (x₀, y₀) hxy₀)) ε hε with ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy hx hy
  have hpdist : dist (x, y) (x₀, y₀) < δ := by
    simp only [Prod.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨hx, hy⟩
  simpa [jointFunction, Real.dist_eq] using hmod hxy hpdist

theorem gap2 (φ : ℝ → ℝ) (a A : ℝ)
    (hφ : ContinuousOn φ (Set.Ioo a A)) :
    ∀ x₀ ∈ Set.Ioo a A, ∀ δ > 0,
      ∃ η > 0, ∀ x ∈ Set.Ioo a A,
        |x - x₀| < η → |φ x - φ x₀| < δ := by
  intro x₀ hx₀ δ hδ
  rcases (Metric.continuousWithinAt_iff.mp
      (hφ x₀ hx₀)) δ hδ with ⟨η, hη, hmod⟩
  refine ⟨η, hη, ?_⟩
  intro x hx hdist
  apply hmod hx
  simpa only [Real.dist_eq] using hdist

theorem gap3 (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (a A b B : ℝ)
    (hf : ContinuousOn (jointFunction f) (rectangle a A b B))
    (hφ : ContinuousOn φ (Set.Ioo a A))
    (hrange : ∀ x ∈ Set.Ioo a A, φ x ∈ Set.Ioo b B) :
    ∀ x₀ ∈ Set.Ioo a A, ∀ ε > 0,
      ∃ η > 0, ∀ x ∈ Set.Ioo a A,
        |x - x₀| < η →
          |f x (φ x) - f x₀ (φ x₀)| < ε := by
  intro x₀ hx₀ ε hε
  have hp₀ : (x₀, φ x₀) ∈ rectangle a A b B := by
    exact ⟨hx₀, hrange x₀ hx₀⟩
  rcases gap1 f a A b B hf x₀ (φ x₀) hp₀ ε hε with
    ⟨δ, hδ, hfδ⟩
  rcases gap2 φ a A hφ x₀ hx₀ δ hδ with
    ⟨η, hη, hφη⟩
  refine ⟨min η δ, lt_min hη hδ, ?_⟩
  intro x hx hclose
  have hrect : (x, φ x) ∈ rectangle a A b B := by
    exact ⟨hx, hrange x hx⟩
  apply hfδ x (φ x) hrect
  · exact lt_of_lt_of_le hclose (min_le_right η δ)
  · apply hφη x hx
    exact lt_of_lt_of_le hclose (min_le_left η δ)

theorem gap4 (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (a A b B : ℝ)
    (hf : ContinuousOn (jointFunction f) (rectangle a A b B))
    (hφ : ContinuousOn φ (Set.Ioo a A))
    (hrange : ∀ x ∈ Set.Ioo a A, φ x ∈ Set.Ioo b B) :
    ∀ x₀ ∈ Set.Ioo a A, ∀ ε > 0,
      ∃ η > 0, ∀ x ∈ Set.Ioo a A,
        |x - x₀| < η →
          |F f φ x - F f φ x₀| < ε := by
  intro x₀ hx₀ ε hε
  simpa [F] using
    (gap3 f φ a A b B hf hφ hrange x₀ hx₀ ε hε)

theorem gap5 (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (a A b B : ℝ)
    (hf : ContinuousOn (jointFunction f) (rectangle a A b B))
    (hφ : ContinuousOn φ (Set.Ioo a A))
    (hrange : ∀ x ∈ Set.Ioo a A, φ x ∈ Set.Ioo b B) :
    ∀ x₀ ∈ Set.Ioo a A, ContinuousAt (F f φ) x₀ := by
  intro x₀ hx₀
  have hwithin : ContinuousWithinAt (F f φ) (Set.Ioo a A) x₀ := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    rcases gap4 f φ a A b B hf hφ hrange x₀ hx₀ ε hε with
      ⟨η, hη, hmod⟩
    refine ⟨η, hη, ?_⟩
    intro x hx hdist
    have habs : |x - x₀| < η := by
      simpa only [Real.dist_eq] using hdist
    have hout := hmod x hx habs
    simpa only [Real.dist_eq] using hout
  exact hwithin.continuousAt (isOpen_Ioo.mem_nhds hx₀)

theorem gap6 (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (a A b B : ℝ)
    (hf : ContinuousOn (jointFunction f) (rectangle a A b B))
    (hφ : ContinuousOn φ (Set.Ioo a A))
    (hrange : ∀ x ∈ Set.Ioo a A, φ x ∈ Set.Ioo b B) :
    ContinuousOn (F f φ) (Set.Ioo a A) := by
  intro x hx
  exact (gap5 f φ a A b B hf hφ hrange x hx).continuousWithinAt

theorem gap7 (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (a A b B : ℝ)
    (hf : ContinuousOn (jointFunction f) (rectangle a A b B))
    (hφ : ContinuousOn φ (Set.Ioo a A))
    (hrange : ∀ x ∈ Set.Ioo a A, φ x ∈ Set.Ioo b B) :
    ContinuousOn (F f φ) (Set.Ioo a A) := by
  exact gap6 f φ a A b B hf hφ hrange

end

end ProofGap.Exercise3209
