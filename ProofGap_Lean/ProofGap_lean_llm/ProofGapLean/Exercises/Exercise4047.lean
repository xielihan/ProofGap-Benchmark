import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4047

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def xCoord (R φ ψ : ℝ) : ℝ :=
  R * Real.cos φ * Real.cos ψ

def yCoord (R φ ψ : ℝ) : ℝ :=
  R * Real.sin φ * Real.cos ψ

def zCoord (R φ ψ : ℝ) : ℝ :=
  R * Real.sin ψ

def dPhi (R φ ψ : ℝ) : Vec3 :=
  (-R * Real.sin φ * Real.cos ψ,
    R * Real.cos φ * Real.cos ψ, 0)

def dPsi (R φ ψ : ℝ) : Vec3 :=
  (-R * Real.cos φ * Real.sin ψ,
    -R * Real.sin φ * Real.sin ψ, R * Real.cos ψ)

def sqNorm (v : Vec3) : ℝ :=
  v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

def dot (u v : Vec3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def E (R φ ψ : ℝ) : ℝ :=
  sqNorm (dPhi R φ ψ)

def G (R φ ψ : ℝ) : ℝ :=
  sqNorm (dPsi R φ ψ)

def F (R φ ψ : ℝ) : ℝ :=
  dot (dPhi R φ ψ) (dPsi R φ ψ)

def areaDensity (R φ ψ : ℝ) : ℝ :=
  Real.sqrt (E R φ ψ * G R φ ψ - F R φ ψ ^ 2)

def surfaceArea (R φ₁ φ₂ ψ₁ ψ₂ : ℝ) : ℝ :=
  ∫ φ in φ₁..φ₂, ∫ ψ in ψ₁..ψ₂, areaDensity R φ ψ

theorem gap1 (R : ℝ) :
    ∀ φ ψ : ℝ, xCoord R φ ψ = R * Real.cos φ * Real.cos ψ := by
  intro φ ψ
  rfl

theorem gap2 (R : ℝ) :
    ∀ φ ψ : ℝ, yCoord R φ ψ = R * Real.sin φ * Real.cos ψ := by
  intro φ ψ
  rfl

theorem gap3 (R φ : ℝ) :
    ∀ ψ : ℝ, zCoord R φ ψ = R * Real.sin ψ := by
  intro ψ
  rfl

theorem gap4 (R φ ψ : ℝ) :
    E R φ ψ = sqNorm (dPhi R φ ψ) := by
  rfl

theorem gap5 (R φ ψ : ℝ) :
    sqNorm (dPhi R φ ψ) =
      R ^ 2 * Real.sin φ ^ 2 * Real.cos ψ ^ 2 +
        R ^ 2 * Real.cos φ ^ 2 * Real.cos ψ ^ 2 := by
  simp [sqNorm, dPhi] <;> ring

theorem gap6 (R φ ψ : ℝ) :
    R ^ 2 * Real.sin φ ^ 2 * Real.cos ψ ^ 2 +
        R ^ 2 * Real.cos φ ^ 2 * Real.cos ψ ^ 2 =
      R ^ 2 * Real.cos ψ ^ 2 := by
  calc
    R ^ 2 * Real.sin φ ^ 2 * Real.cos ψ ^ 2 +
        R ^ 2 * Real.cos φ ^ 2 * Real.cos ψ ^ 2 =
      R ^ 2 * Real.cos ψ ^ 2 *
        (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
    _ = R ^ 2 * Real.cos ψ ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

theorem gap7 (R φ ψ : ℝ) :
    E R φ ψ = R ^ 2 * Real.cos ψ ^ 2 := by
  calc
    E R φ ψ = sqNorm (dPhi R φ ψ) := gap4 R φ ψ
    _ = R ^ 2 * Real.sin φ ^ 2 * Real.cos ψ ^ 2 +
        R ^ 2 * Real.cos φ ^ 2 * Real.cos ψ ^ 2 := gap5 R φ ψ
    _ = R ^ 2 * Real.cos ψ ^ 2 := gap6 R φ ψ

theorem gap8 (R φ ψ : ℝ) :
    G R φ ψ = sqNorm (dPsi R φ ψ) := by
  rfl

theorem gap9 (R φ ψ : ℝ) :
    sqNorm (dPsi R φ ψ) = R ^ 2 := by
  change
    (-R * Real.cos φ * Real.sin ψ) ^ 2 +
        (-R * Real.sin φ * Real.sin ψ) ^ 2 +
          (R * Real.cos ψ) ^ 2 = R ^ 2
  calc
    (-R * Real.cos φ * Real.sin ψ) ^ 2 +
        (-R * Real.sin φ * Real.sin ψ) ^ 2 +
          (R * Real.cos ψ) ^ 2 =
      R ^ 2 *
        ((Real.sin φ ^ 2 + Real.cos φ ^ 2) * Real.sin ψ ^ 2 +
          Real.cos ψ ^ 2) := by ring
    _ = R ^ 2 := by simp [Real.sin_sq_add_cos_sq]

theorem gap10 (R φ ψ : ℝ) :
    G R φ ψ = R ^ 2 := by
  calc
    G R φ ψ = sqNorm (dPsi R φ ψ) := gap8 R φ ψ
    _ = R ^ 2 := gap9 R φ ψ

theorem gap11 (R φ ψ : ℝ) :
    F R φ ψ = dot (dPhi R φ ψ) (dPsi R φ ψ) := by
  rfl

theorem gap12 (R φ ψ : ℝ) :
    dot (dPhi R φ ψ) (dPsi R φ ψ) = 0 := by
  simp [dot, dPhi, dPsi] <;> ring

theorem gap13 (R φ ψ : ℝ) :
    F R φ ψ = 0 := by
  calc
    F R φ ψ = dot (dPhi R φ ψ) (dPsi R φ ψ) := gap11 R φ ψ
    _ = 0 := gap12 R φ ψ

theorem gap14 (R φ ψ : ℝ) (hR : 0 < R)
    (hψ₁ : -Real.pi / 2 ≤ ψ) (hψ₂ : ψ ≤ Real.pi / 2) :
    areaDensity R φ ψ = R ^ 2 * Real.cos ψ := by
  have hcos : 0 ≤ Real.cos ψ := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · calc
        -(Real.pi / 2) = -Real.pi / 2 := by ring
        _ ≤ ψ := hψ₁
    · exact hψ₂
  unfold areaDensity
  rw [gap7 R φ ψ, gap10 R φ ψ, gap13 R φ ψ]
  calc
    Real.sqrt
        (R ^ 2 * Real.cos ψ ^ 2 * R ^ 2 - 0 ^ 2) =
      Real.sqrt ((R ^ 2 * Real.cos ψ) ^ 2) := by
        congr 1
        ring
    _ = |R ^ 2 * Real.cos ψ| := Real.sqrt_sq_eq_abs _
    _ = R ^ 2 * Real.cos ψ :=
      abs_of_nonneg (mul_nonneg (sq_nonneg R) hcos)

theorem gap15 (R φ₁ φ₂ ψ₁ ψ₂ : ℝ) (hR : 0 < R)
    (hφ : φ₁ ≤ φ₂)
    (hψ₁ : -Real.pi / 2 ≤ ψ₁) (hψ₂ : ψ₂ ≤ Real.pi / 2)
    (hψ : ψ₁ ≤ ψ₂) :
    surfaceArea R φ₁ φ₂ ψ₁ ψ₂ =
      ∫ φ in φ₁..φ₂, ∫ ψ in ψ₁..ψ₂, R ^ 2 * Real.cos ψ := by
  unfold surfaceArea
  apply intervalIntegral.integral_congr
  intro φ _
  apply intervalIntegral.integral_congr
  intro ψ hψmem
  have hψmem' : ψ ∈ Set.Icc ψ₁ ψ₂ := by
    simpa [Set.uIcc_of_le hψ] using hψmem
  exact gap14 R φ ψ hR
    (le_trans hψ₁ hψmem'.1)
    (le_trans hψmem'.2 hψ₂)

theorem gap16 (R φ₁ φ₂ ψ₁ ψ₂ : ℝ) (hR : 0 < R)
    (hφ : φ₁ ≤ φ₂)
    (hψ₁ : -Real.pi / 2 ≤ ψ₁) (hψ₂ : ψ₂ ≤ Real.pi / 2)
    (hψ : ψ₁ ≤ ψ₂) :
    surfaceArea R φ₁ φ₂ ψ₁ ψ₂ =
      (φ₂ - φ₁) * (Real.sin ψ₂ - Real.sin ψ₁) * R ^ 2 := by
  rw [gap15 R φ₁ φ₂ ψ₁ ψ₂ hR hφ hψ₁ hψ₂ hψ]
  have hcos : (∫ x in ψ₁..ψ₂, Real.cos x) =
      Real.sin ψ₂ - Real.sin ψ₁ := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sin x)
      (Real.continuous_cos.intervalIntegrable ψ₁ ψ₂)
  rw [intervalIntegral.integral_const_mul, hcos]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

end

end ProofGap.Exercise4047
