import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise808_1

noncomputable section

def f (x : ℝ) : ℝ := x ^ 3
def oscSet (δ : ℝ) : Set ℝ :=
  {|f x - f y| | (x ∈ Set.Icc (0 : ℝ) 1) (y ∈ Set.Icc (0 : ℝ) 1)
    (h : |x - y| ≤ δ)}
def ω (δ : ℝ) : ℝ := sSup (oscSet δ)

theorem gap1 (x₁ x₂ : ℝ) :
    |x₁ ^ 3 - x₂ ^ 3| =
      |x₁ - x₂| * |x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2| := by
  rw [← abs_mul]
  congr 1
  ring
theorem gap2 (δ x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (0 : ℝ) 1) (hd : |x₁ - x₂| ≤ δ) :
    |x₁ - x₂| * |x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2| ≤ 3 * δ := by
  rcases hx₁ with ⟨hx₁0, hx₁1⟩
  rcases hx₂ with ⟨hx₂0, hx₂1⟩
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg (x₁ - x₂)) hd
  have hsq₁ : x₁ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x₁ - 1)]
  have hsq₂ : x₂ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x₂ - 1)]
  have hmul : x₁ * x₂ ≤ 1 := by nlinarith
  have hsum0 : 0 ≤ x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 := by positivity
  have hsum3 : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 ≤ 3 := by linarith
  rw [abs_of_nonneg hsum0]
  nlinarith [abs_nonneg (x₁ - x₂)]
theorem gap3 (δ x₁ x₂ : ℝ) (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1)
    (hx₂ : x₂ ∈ Set.Icc (0 : ℝ) 1) (hd : |x₁ - x₂| ≤ δ) :
    |x₁ ^ 3 - x₂ ^ 3| ≤ 3 * δ := by
  rw [gap1]
  exact gap2 δ x₁ x₂ hx₁ hx₂ hd
theorem gap4 (δ : ℝ) (hδ : 0 ≤ δ) : ω δ ≤ 3 * δ := by
  unfold ω
  apply csSup_le
  · refine ⟨0, ?_⟩
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, 0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · simpa using hδ
    · simp [f]
  · rintro z ⟨x₁, hx₁, x₂, hx₂, hd, rfl⟩
    exact gap3 δ x₁ x₂ hx₁ hx₂ hd
theorem gap5 (δ : ℝ) (hδ : 0 ≤ δ) :
    let C : ℝ := 3
    let α : ℕ := 1
    ω δ ≤ C * δ ^ α := by
  dsimp
  simpa using gap4 δ hδ

end

end ProofGap.Exercise808_1
