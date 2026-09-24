import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise382_1

noncomputable section

def domain : Set ℝ := Set.Ioo 0 1
def f (x : ℝ) : ℝ := 1 / x

def BoundedOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ s, |g x| ≤ M

def LocallyBoundedOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x₀ ∈ s, ∃ δ : ℝ, 0 < δ ∧
    BoundedOn g (Set.Ioo (x₀ - δ) (x₀ + δ) ∩ s)

def ExampleProperties (g : ℝ → ℝ) : Prop :=
  LocallyBoundedOn g domain ∧ ¬BoundedOn g domain

/-- Source: `proof_gap/exercise_382_1/1.txt`. -/
theorem gap1 (h : ExampleProperties f) : domain = Set.Ioo 0 1 := by
  rfl

/-- Source: `proof_gap/exercise_382_1/2.txt`. -/
theorem gap2 (h : ExampleProperties f) : LocallyBoundedOn f domain := by
  exact h.1

/-- Source: `proof_gap/exercise_382_1/3.txt`. -/
theorem gap3 (h : ExampleProperties f) : ¬BoundedOn f domain := by
  exact h.2

/-- Source: `proof_gap/exercise_382_1/4.txt`. -/
theorem gap4 : ExampleProperties f := by
  constructor
  · intro x₀ hx₀
    change x₀ ∈ Set.Ioo 0 1 at hx₀
    rcases hx₀ with ⟨hx₀_pos, hx₀_lt⟩
    refine ⟨x₀ / 2, by linarith, ?_⟩
    refine ⟨2 / x₀, ?_⟩
    intro x hx
    rcases hx.1 with ⟨hx_lower, hx_upper⟩
    have hx_pos : 0 < x := by
      linarith
    change |1 / x| ≤ 2 / x₀
    rw [abs_of_pos (one_div_pos.mpr hx_pos)]
    rw [div_le_div_iff₀ hx_pos hx₀_pos]
    linarith
  · intro hbounded
    rcases hbounded with ⟨M, hM⟩
    let x : ℝ := 1 / (|M| + 2)
    have hden_pos : 0 < |M| + 2 := by
      linarith [abs_nonneg M]
    have hx_pos : 0 < x := by
      dsimp [x]
      exact one_div_pos.mpr hden_pos
    have hx_lt_one : x < 1 := by
      dsimp [x]
      rw [div_lt_iff₀ hden_pos]
      linarith [abs_nonneg M]
    have hbound : |f x| ≤ M := hM x (by
      change x ∈ Set.Ioo 0 1
      exact ⟨hx_pos, hx_lt_one⟩)
    have hfx : f x = |M| + 2 := by
      simp [f, x]
    rw [hfx, abs_of_pos hden_pos] at hbound
    linarith [le_abs_self M]

end

end ProofGap.Exercise382_1
