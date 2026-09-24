import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise823

noncomputable section

def y₁ (a b x : ℝ) : ℝ := a * x + b
def y₂ (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c
def y₃ (a x : ℝ) : ℝ := Real.rpow a x
def increment (h : ℝ → ℝ) (x Δx : ℝ) : ℝ := h (x + Δx) - h x

/-- Source: `proof_gap/exercise_823/1.txt`; bind `Δy₁` by its intended
increment definition. -/
theorem gap1 (a b x Δx Δy₁ : ℝ)
    (hΔ : Δy₁ = increment (y₁ a b) x Δx) :
    Δy₁ = a * x + a * Δx + b - (a * x + b) := by
  rw [hΔ]
  unfold increment y₁
  ring

/-- Source: `proof_gap/exercise_823/2.txt`. -/
theorem gap2 (a b x Δx : ℝ) :
    a * x + a * Δx + b - (a * x + b) = a * Δx := by
  ring

/-- Source: `proof_gap/exercise_823/3.txt`; bind `Δy₁`. -/
theorem gap3 (a b x Δx Δy₁ : ℝ)
    (hΔ : Δy₁ = increment (y₁ a b) x Δx) :
    Δy₁ = a * Δx := by
  calc
    Δy₁ = a * x + a * Δx + b - (a * x + b) := gap1 a b x Δx Δy₁ hΔ
    _ = a * Δx := gap2 a b x Δx

/-- Source: `proof_gap/exercise_823/4.txt`; bind `Δy₂`. -/
theorem gap4 (a b c x Δx Δy₂ : ℝ)
    (hΔ : Δy₂ = increment (y₂ a b c) x Δx) :
    Δy₂ = a * (x + Δx) ^ 2 + b * (x + Δx) + c -
      (a * x ^ 2 + b * x + c) := by
  simpa [increment, y₂] using hΔ

/-- Source: `proof_gap/exercise_823/5.txt`. -/
theorem gap5 (a b c x Δx : ℝ) :
    a * (x + Δx) ^ 2 + b * (x + Δx) + c -
        (a * x ^ 2 + b * x + c) =
      (2 * a * x + b) * Δx + a * Δx ^ 2 := by
  ring

/-- Source: `proof_gap/exercise_823/6.txt`; bind `Δy₂`. -/
theorem gap6 (a b c x Δx Δy₂ : ℝ)
    (hΔ : Δy₂ = increment (y₂ a b c) x Δx) :
    Δy₂ = (2 * a * x + b) * Δx + a * Δx ^ 2 := by
  calc
    Δy₂ = a * (x + Δx) ^ 2 + b * (x + Δx) + c -
        (a * x ^ 2 + b * x + c) := gap4 a b c x Δx Δy₂ hΔ
    _ = (2 * a * x + b) * Δx + a * Δx ^ 2 := gap5 a b c x Δx

/-- Source: `proof_gap/exercise_823/7.txt`; bind `Δy₃`. -/
theorem gap7 (a x Δx Δy₃ : ℝ)
    (hΔ : Δy₃ = increment (y₃ a) x Δx) :
    Δy₃ = Real.rpow a (x + Δx) - Real.rpow a x := by
  simpa [increment, y₃] using hΔ

/-- Source: `proof_gap/exercise_823/8.txt`; interpret real exponents by
`Real.rpow` and add `a>0`. -/
theorem gap8 (a x Δx : ℝ) (ha : 0 < a) :
    Real.rpow a (x + Δx) - Real.rpow a x =
      Real.rpow a x * (Real.rpow a Δx - 1) := by
  change a ^ (x + Δx) - a ^ x = a ^ x * (a ^ Δx - 1)
  rw [Real.rpow_add ha]
  ring

/-- Source: `proof_gap/exercise_823/9.txt`; bind `Δy₃` and add `a>0`. -/
theorem gap9 (a x Δx Δy₃ : ℝ) (ha : 0 < a)
    (hΔ : Δy₃ = increment (y₃ a) x Δx) :
    Δy₃ = Real.rpow a x * (Real.rpow a Δx - 1) := by
  calc
    Δy₃ = Real.rpow a (x + Δx) - Real.rpow a x := gap7 a x Δx Δy₃ hΔ
    _ = Real.rpow a x * (Real.rpow a Δx - 1) := gap8 a x Δx ha

end

end ProofGap.Exercise823
