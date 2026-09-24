import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1076

noncomputable section

def C₁ (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ^ 2 = 4 * a * (a - p.1) ∧ 0 < a}

def C₂ (b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ^ 2 = 4 * b * (b + p.1) ∧ 0 < b}

def k₁ (a y : ℝ) : ℝ := -(2 * a / y)
def k₂ (b y : ℝ) : ℝ := 2 * b / y

private theorem common_y_ne_zero (a b x y : ℝ)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) : y ≠ 0 := by
  have ha : 0 < a := hmem.1.2
  have hb : 0 < b := hmem.2.2
  have h₁ := hmem.1.1
  have h₂ := hmem.2.1
  intro hy
  rw [hy] at h₁ h₂
  norm_num at h₁ h₂
  rcases h₁ with ha0 | hax
  · nlinarith
  rcases h₂ with hb0 | hbx
  · nlinarith
  · nlinarith

theorem gap1 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    2 * y * k₁ a y = -4 * a := by
  have hy : y ≠ 0 := common_y_ne_zero a b x y hmem
  simp only [k₁]
  field_simp [hy]
  <;> ring

theorem gap2 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ a y = -(2 * a / y) := by
  rfl

theorem gap3 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    2 * y * k₂ b y = 4 * b := by
  have hy : y ≠ 0 := common_y_ne_zero a b x y hmem
  simp only [k₂]
  field_simp [hy]
  <;> ring

theorem gap4 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₂ b y = 2 * b / y := by
  rfl

theorem gap5 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ a y * k₂ b y = -(4 * a * b / y ^ 2) := by
  have hy : y ≠ 0 := common_y_ne_zero a b x y hmem
  simp only [k₁, k₂]
  field_simp [hy]
  <;> ring

theorem gap6 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    4 * a * (a - x) = 4 * b * (b + x) := by
  exact hmem.1.1.symm.trans hmem.2.1

theorem gap7 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    x = a - b := by
  have ha : 0 < a := hmem.1.2
  have hb : 0 < b := hmem.2.2
  have heq := gap6 a b x y hmem
  nlinarith

theorem gap8 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    y ^ 2 = 4 * a * (a - a + b) := by
  calc
    y ^ 2 = 4 * a * (a - x) := hmem.1.1
    _ = 4 * a * (a - a + b) := by
      rw [gap7 a b x y hmem]
      ring

theorem gap9 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    4 * a * (a - a + b) = 4 * a * b := by
  ring

theorem gap10 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    y ^ 2 = 4 * a * b := by
  exact (gap8 a b x y hmem).trans (gap9 a b x y hmem)

theorem gap11 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ a y * k₂ b y = -1 := by
  calc
    k₁ a y * k₂ b y = -(4 * a * b / y ^ 2) := gap5 a b x y hmem
    _ = -(y ^ 2 / y ^ 2) := by rw [gap10 a b x y hmem]
    _ = -1 := by
      have hy : y ≠ 0 := common_y_ne_zero a b x y hmem
      field_simp [hy]

theorem gap12 (a b x y : ℝ) (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ a y * k₂ b y = -1 := by
  exact gap11 a b x y hmem

end

end ProofGap.Exercise1076
