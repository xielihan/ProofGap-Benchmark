import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology ENNReal
open Filter MeasureTheory Set intervalIntegral

/-!
exercise: exercise_4186
Original problem: convergence of a parameter-dependent improper integral.
-/

noncomputable section

variable (a A b B p c : ℝ) (φ : ℝ × ℝ → ℝ) (f F : ℝ → ℝ)

def rect4186 : Set (ℝ × ℝ) := Icc a A ×ˢ Icc b B
def extendedRect4186 : Set (ℝ × ℝ) := Icc a A ×ˢ Icc (b - 2 * c) (B + 2 * c)
def singularKernel4186 (p : ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ := 1 / |f x - y| ^ p
def inner4186 (p : ℝ) (φ : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ := φ (x, y) / |f x - y| ^ p

theorem proof_gap_exercise_4186_1 (hp : p < 1) :
    ∀ x ∈ Icc a A, f x ∈ Icc b B → IntegrableOn (fun y => singularKernel4186 p f x y) (Icc b B) volume := by sorry

theorem proof_gap_exercise_4186_2 (hp : p < 1) :
    ∀ x ∈ Icc a A, f x ∉ Icc b B → IntegrableOn (fun y => singularKernel4186 p f x y) (Icc b B) volume := by sorry

theorem proof_gap_exercise_4186_3 (hp : p < 1) (hφ : ContinuousOn φ (rect4186 a A b B)) :
    ∀ x ∈ Icc a A, IntegrableOn (fun y => inner4186 p φ f x y) (Icc b B) volume := by sorry

theorem proof_gap_exercise_4186_4 (hφ : ContinuousOn φ (rect4186 a A b B)) :
    ContinuousOn φ (rect4186 a A b B) := by sorry

theorem proof_gap_exercise_4186_5 (hf : ContinuousOn f (Icc a A)) :
    ContinuousOn (fun z : ℝ × ℝ => |f z.1 - z.2| ^ (1 - p)) (extendedRect4186 a A b B c) := by sorry

theorem proof_gap_exercise_4186_6 (hφ : ContinuousOn φ (extendedRect4186 a A b B c)) :
    UniformContinuousOn φ (extendedRect4186 a A b B c) := by sorry

theorem proof_gap_exercise_4186_7 (hf : ContinuousOn f (Icc a A)) :
    UniformContinuousOn (fun z : ℝ × ℝ => |f z.1 - z.2| ^ (1 - p)) (extendedRect4186 a A b B c) := by sorry

theorem proof_gap_exercise_4186_8 :
    ∃ M > 0, ∀ x y : ℝ, (x, y) ∈ extendedRect4186 a A b B c →
      |φ (x, y)| ≤ M ∧ |f x - y| ^ (1 - p) ≤ M := by sorry

theorem proof_gap_exercise_4186_9 :
    ∀ ε > 0, ∃ δ₁ > 0, δ₁ < (ε / 2) ^ (1 / (1 - p)) ∧
      ∀ x₁ x₂ y₁ y₂ : ℝ, (x₁, y₁) ∈ extendedRect4186 a A b B c →
        (x₂, y₂) ∈ extendedRect4186 a A b B c → |x₁ - x₂| < δ₁ → |y₁ - y₂| < δ₁ →
          |φ (x₁, y₁) - φ (x₂, y₂)| < ε ∧
          abs (|f x₁ - y₁| ^ (1 - p) - |f x₂ - y₂| ^ (1 - p)) < ε := by sorry

theorem proof_gap_exercise_4186_10 :
    ∀ ε > 0, ∃ δ₁ > 0, ∃ δ₂ > 0, ∀ x₁ x₂ : ℝ,
      x₁ ∈ Icc a A → x₂ ∈ Icc a A → |x₁ - x₂| < δ₂ → |f x₁ - f x₂| < δ₁ := by sorry

theorem proof_gap_exercise_4186_11 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ ≥ f x₂ → ∀ u : ℝ, b - c ≤ u ∧ u ≤ B + c →
        |φ (x₁, u + f x₁) - φ (x₂, u + f x₂)| < ε := by sorry

theorem proof_gap_exercise_4186_12 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ ≥ f x₂ →
      F x₁ - F x₂ =
        (∫ u in (b - f x₁)..(B - f x₂), (φ (x₁, u + f x₁) - φ (x₂, u + f x₂)) / |u| ^ p) -
        (∫ u in (B - f x₁)..(B - f x₂), φ (x₁, u + f x₁) / |u| ^ p) +
        (∫ u in (b - f x₁)..(b - f x₂), φ (x₂, u + f x₂) / |u| ^ p) := by sorry

theorem proof_gap_exercise_4186_13 :
    ∀ ε > 0, ∃ δ > 0, ∃ I₁ I₂ I₃ : ℝ, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ ≥ f x₂ → F x₁ - F x₂ = I₁ - I₂ + I₃ := by sorry

theorem proof_gap_exercise_4186_14 :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A → |x₁ - x₂| < δ →
      f x₁ ≥ f x₂ → ∀ α β : ℝ, p < 1 ∧ α ≤ β →
        ∫ u in α..β, 1 / |u| ^ p ≤ (1 / (1 - p)) * (|β| ^ (1 - p) + |α| ^ (1 - p)) := by sorry

theorem proof_gap_exercise_4186_15 :
    ∀ ε > 0, ∃ δ > 0, ∃ I₁ : ℝ, ∃ M > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ ≥ f x₂ → |I₁| < (2 * M * ε) / (1 - p) := by sorry

theorem proof_gap_exercise_4186_16 :
    ∀ ε > 0, ∃ δ > 0, ∃ I₂ : ℝ, ∃ M > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ ≥ f x₂ → |I₂| < (M * ε) / (1 - p) := by sorry

theorem proof_gap_exercise_4186_17 :
    ∀ ε > 0, ∃ δ > 0, ∃ I₃ : ℝ, ∃ M > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ ≥ f x₂ → |I₃| < (M * ε) / (1 - p) := by sorry

theorem proof_gap_exercise_4186_18 :
    ∀ ε > 0, ∃ δ > 0, ∃ M > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ ≥ f x₂ → |F x₁ - F x₂| < (4 * M * ε) / (1 - p) := by sorry

theorem proof_gap_exercise_4186_19 :
    ∀ ε > 0, ∃ δ > 0, ∃ M > 0, ∀ x₁ x₂ : ℝ, x₁ ∈ Icc a A → x₂ ∈ Icc a A →
      |x₁ - x₂| < δ → f x₁ < f x₂ → |F x₁ - F x₂| < (4 * M * ε) / (1 - p) := by sorry

theorem proof_gap_exercise_4186_20 :
    ContinuousOn F (Icc a A) := by sorry

theorem proof_gap_exercise_4186_21 :
    ContinuousOn F (Icc a A) := by sorry

theorem proof_gap_exercise_4186_22 :
    (∫ x in a..A, ∫ y in b..B, inner4186 p φ f x y) = ∫ x in a..A, F x := by sorry

theorem proof_gap_exercise_4186_23 :
    IntegrableOn F (Icc a A) volume := by sorry

theorem proof_gap_exercise_4186_24 :
    IntegrableOn (fun x => ∫ y in b..B, inner4186 p φ f x y) (Icc a A) volume := by sorry

theorem proof_gap_exercise_4186_25 :
    IntegrableOn (fun x => ∫ y in b..B, inner4186 p φ f x y) (Icc a A) volume := by sorry
