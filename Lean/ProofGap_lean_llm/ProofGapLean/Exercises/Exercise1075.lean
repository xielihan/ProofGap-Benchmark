import ProofGapLean.Prelude.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1075

noncomputable section

def C₁ (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 - p.2 ^ 2 = a}

def C₂ (b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 * p.2 = b}

def k₁ (x y : ℝ) : ℝ := x / y
def k₂ (x y : ℝ) : ℝ := -(y / x)

private theorem coords_ne_zero (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) : x ≠ 0 ∧ y ≠ 0 := by
  have hxy : x * y = b := hmem.2
  constructor
  · intro hx
    apply hb
    calc
      b = x * y := hxy.symm
      _ = 0 := by rw [hx, zero_mul]
  · intro hy
    apply hb
    calc
      b = x * y := hxy.symm
      _ = 0 := by rw [hy, mul_zero]

theorem gap1 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    2 * x - 2 * y * k₁ x y = 0 := by
  have hy : y ≠ 0 := (coords_ne_zero a b x y hb hmem).2
  unfold k₁
  field_simp [hy] <;> ring

theorem gap2 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ x y = x / y := by
  rfl

theorem gap3 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    y + x * k₂ x y = 0 := by
  have hx : x ≠ 0 := (coords_ne_zero a b x y hb hmem).1
  unfold k₂
  field_simp [hx] <;> ring

theorem gap4 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₂ x y = -(y / x) := by
  rfl

theorem gap5 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ x y * k₂ x y = (x / y) * (-(y / x)) := by
  rfl

theorem gap6 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    (x / y) * (-(y / x)) = -1 := by
  have hne := coords_ne_zero a b x y hb hmem
  field_simp [hne.1, hne.2] <;> ring

theorem gap7 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ x y * k₂ x y = -1 := by
  calc
    k₁ x y * k₂ x y = (x / y) * (-(y / x)) := gap5 a b x y hb hmem
    _ = -1 := gap6 a b x y hb hmem

theorem gap8 (a b x y : ℝ) (hb : b ≠ 0)
    (hmem : (x, y) ∈ C₁ a ∩ C₂ b) :
    k₁ x y * k₂ x y = -1 := by
  exact gap7 a b x y hb hmem

end

end ProofGap.Exercise1075
