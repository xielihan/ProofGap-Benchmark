import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3208

noncomputable section

open scoped Topology

def rectangle (a A b B : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc a A ×ˢ Set.Icc b B

def jointFunction (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f p.1 p.2

def F (f : ℝ → ℝ → ℝ) (φ : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f x (φ n x)

def UniformConvergesOn
    (u : ℕ → ℝ → ℝ) (u₀ : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - u₀ x| < ε

def UniformCauchyOn (u : ℕ → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ s,
    |u n x - u m x| < ε

theorem gap1 (f : ℝ → ℝ → ℝ) (φ : ℕ → ℝ → ℝ) :
    ∀ n x, F f φ n x = f x (φ n x) := by
  intro n x
  rfl

theorem gap2 (f : ℝ → ℝ → ℝ) (a A b B : ℝ)
    (hf : ContinuousOn (jointFunction f) (rectangle a A b B)) :
    UniformContinuousOn (jointFunction f) (rectangle a A b B) := by
  exact
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hf

theorem gap3 (f : ℝ → ℝ → ℝ) (a A b B : ℝ)
    (hf : UniformContinuousOn (jointFunction f) (rectangle a A b B)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ y₁ x₂ y₂ : ℝ,
      (x₁, y₁) ∈ rectangle a A b B →
      (x₂, y₂) ∈ rectangle a A b B →
      |x₁ - x₂| < δ → |y₁ - y₂| < δ →
        |f x₁ y₁ - f x₂ y₂| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := (Metric.uniformContinuousOn_iff.mp hf) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x₁ y₁ x₂ y₂ hp₁ hp₂ hx hy
  have hpdist : dist (x₁, y₁) (x₂, y₂) < δ := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff] using And.intro hx hy
  have hout := h (x₁, y₁) hp₁ (x₂, y₂) hp₂ hpdist
  simpa only [jointFunction, Real.dist_eq] using hout

theorem gap4 (f : ℝ → ℝ → ℝ) (a A b B : ℝ)
    (hf : UniformContinuousOn (jointFunction f) (rectangle a A b B)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y₁ y₂ : ℝ,
      x ∈ Set.Icc a A → y₁ ∈ Set.Icc b B → y₂ ∈ Set.Icc b B →
      |y₁ - y₂| < δ → |f x y₁ - f x y₂| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := gap3 f a A b B hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y₁ y₂ hx hy₁ hy₂ hy
  apply h x y₁ x y₂
  · exact ⟨hx, hy₁⟩
  · exact ⟨hx, hy₂⟩
  · simpa using hδ
  · exact hy

theorem gap5 (φ : ℕ → ℝ → ℝ) (φ₀ : ℝ → ℝ) (a A : ℝ)
    (hφ : UniformConvergesOn φ φ₀ (Set.Icc a A)) :
    ∀ δ > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ Set.Icc a A,
      |φ n x - φ m x| < δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hφ (δ / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro m hm n hn x hx
  have hn' : |φ n x - φ₀ x| < δ / 2 := hN n hn x hx
  have hm' : |φ₀ x - φ m x| < δ / 2 := by
    simpa only [abs_sub_comm] using hN m hm x hx
  have htri :
      |φ n x - φ m x| ≤ |φ n x - φ₀ x| + |φ₀ x - φ m x| := by
    simpa only [Real.dist_eq] using
      (dist_triangle (φ n x) (φ₀ x) (φ m x))
  linarith

theorem gap6 (f : ℝ → ℝ → ℝ) (φ : ℕ → ℝ → ℝ)
    (φ₀ : ℝ → ℝ) (a A b B : ℝ)
    (hf : UniformContinuousOn (jointFunction f) (rectangle a A b B))
    (hφ : UniformConvergesOn φ φ₀ (Set.Icc a A))
    (hrange : ∀ n ≥ 1, ∀ x, x ∈ Set.Icc a A → φ n x ∈ Set.Icc b B) :
    UniformCauchyOn (F f φ) (Set.Icc a A) := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := gap4 f a A b B hf ε hε
  obtain ⟨N, hN⟩ := gap5 φ φ₀ a A hφ δ hδ
  refine ⟨max N 1, ?_⟩
  intro m hm n hn x hx
  have hmN : N ≤ m := le_trans (Nat.le_max_left N 1) hm
  have hnN : N ≤ n := le_trans (Nat.le_max_left N 1) hn
  have hm1 : 1 ≤ m := le_trans (Nat.le_max_right N 1) hm
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right N 1) hn
  have hrm : φ m x ∈ Set.Icc b B := hrange m hm1 x hx
  have hrn : φ n x ∈ Set.Icc b B := hrange n hn1 x hx
  have hφnm : |φ n x - φ m x| < δ := hN m hmN n hnN x hx
  simpa only [F] using hfδ x (φ n x) (φ m x) hx hrn hrm hφnm

theorem gap7 (u : ℕ → ℝ → ℝ) (a A : ℝ)
    (hu : UniformCauchyOn u (Set.Icc a A)) :
    ∃ u₀ : ℝ → ℝ, UniformConvergesOn u u₀ (Set.Icc a A) := by
  classical
  have hcauchy : ∀ x ∈ Set.Icc a A, CauchySeq (fun n => u n x) := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    simpa only [Real.dist_eq] using hN n hn m hm x hx
  let u₀ : ℝ → ℝ := fun x =>
    if hx : x ∈ Set.Icc a A then
      Classical.choose (cauchySeq_tendsto_of_complete (hcauchy x hx))
    else 0
  have hu₀ : ∀ x (hx : x ∈ Set.Icc a A),
      Tendsto (fun n => u n x) atTop (nhds (u₀ x)) := by
    intro x hx
    dsimp [u₀]
    rw [dif_pos hx]
    exact Classical.choose_spec
      (cauchySeq_tendsto_of_complete (hcauchy x hx))
  refine ⟨u₀, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn x hx
  have ht : Tendsto (fun m : ℕ => |u n x - u m x|) atTop
      (nhds |u n x - u₀ x|) :=
    (tendsto_const_nhds.sub (hu₀ x hx)).abs
  have hev : ∀ᶠ m : ℕ in atTop, |u n x - u m x| ≤ ε / 2 :=
    (Filter.eventually_ge_atTop N).mono fun m hm =>
      le_of_lt (hN m hm n hn x hx)
  have hle : |u n x - u₀ x| ≤ ε / 2 := le_of_tendsto ht hev
  linarith

theorem gap8 (u : ℕ → ℝ → ℝ) (a A : ℝ)
    (hu : UniformCauchyOn u (Set.Icc a A)) :
    ∃ u₀ : ℝ → ℝ, UniformConvergesOn u u₀ (Set.Icc a A) := by
  exact gap7 u a A hu

end

end ProofGap.Exercise3208
