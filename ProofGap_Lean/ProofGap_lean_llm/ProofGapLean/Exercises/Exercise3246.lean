import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3246

noncomputable section

def area (x y : ℝ) : ℝ := x * y

def distance (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2)

def areaLinearEstimate (x y dx dy : ℝ) : ℝ :=
  y * dx + x * dy

def distanceLinearEstimate (x y dx dy : ℝ) : ℝ :=
  (x * dx + y * dy) / distance x y

def x₀ : ℝ := 6000
def y₀ : ℝ := 8000
def dx : ℝ := 2
def dy : ℝ := -5

def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance

theorem gap1 :
    areaLinearEstimate x₀ y₀ dx dy = y₀ * dx + x₀ * dy := by
  rfl

theorem gap2 :
    distanceLinearEstimate x₀ y₀ dx dy =
      (x₀ * dx + y₀ * dy) / Real.sqrt (x₀ ^ 2 + y₀ ^ 2) := by
  rfl

theorem gap3 :
    areaLinearEstimate x₀ y₀ dx dy = 8000 * 2 + 6000 * (-5) := by
  rfl

theorem gap4 :
    (8000 : ℝ) * 2 + 6000 * (-5) = -14000 := by
  norm_num

theorem gap5 :
    areaLinearEstimate x₀ y₀ dx dy = -14000 := by
  calc
    areaLinearEstimate x₀ y₀ dx dy = 8000 * 2 + 6000 * (-5) := gap3
    _ = -14000 := gap4

theorem gap6 :
    distanceLinearEstimate x₀ y₀ dx dy =
      (6000 * 2 + 8000 * (-5)) /
        Real.sqrt (6000 ^ 2 + 8000 ^ 2) := by
  rfl

theorem gap7 :
    ((6000 : ℝ) * 2 + 8000 * (-5)) /
        Real.sqrt (6000 ^ 2 + 8000 ^ 2) =
      -2.8 := by
  have hrad : (6000 : ℝ) ^ 2 + 8000 ^ 2 = 10000 ^ 2 := by
    norm_num
  rw [hrad, Real.sqrt_sq_eq_abs]
  norm_num

theorem gap8 :
    distanceLinearEstimate x₀ y₀ dx dy = -2.8 := by
  calc
    distanceLinearEstimate x₀ y₀ dx dy =
        ((6000 : ℝ) * 2 + 8000 * (-5)) /
          Real.sqrt (6000 ^ 2 + 8000 ^ 2) := gap6
    _ = -2.8 := gap7

theorem gap9 :
    Approx (distanceLinearEstimate x₀ y₀ dx dy) (-3) (1 / 2) := by
  unfold Approx
  rw [gap8]
  norm_num

theorem gap10 :
    areaLinearEstimate x₀ y₀ dx dy = -14000 := by
  exact gap5

end

end ProofGap.Exercise3246
