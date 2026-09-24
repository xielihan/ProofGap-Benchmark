import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace ProofGap.Exercise4127

noncomputable section

open MeasureTheory
open scoped Interval Matrix

abbrev Point3 := Fin 3 → ℝ

def coordinateTransform (A : Matrix (Fin 3) (Fin 3) ℝ) (p : Point3) : Point3 :=
  A.mulVec p

def coordinateJacobian
    (F : Point3 → Point3) (p : Point3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => deriv (fun t => F (Function.update p j t) i) (p j)

def jacobianDeterminant (F : Point3 → Point3) (p : Point3) : ℝ :=
  Matrix.det (coordinateJacobian F p)

def axisBox (h : Point3) : Set Point3 :=
  {q | ∀ i, -h i ≤ q i ∧ q i ≤ h i}

def transformedSolid (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Point3) : Set Point3 :=
  coordinateTransform A ⁻¹' axisBox h

def volumeReal (V : Set Point3) : ℝ :=
  (MeasureTheory.volume V).toReal

theorem gap1 (A : Matrix (Fin 3) (Fin 3) ℝ) (p : Point3) :
    jacobianDeterminant (coordinateTransform A) p = Matrix.det A := by
  unfold jacobianDeterminant
  apply congrArg Matrix.det
  funext i j
  unfold coordinateJacobian
  apply HasDerivAt.deriv
  have hs :
      HasDerivAt
        (fun t : ℝ => ∑ k : Fin 3, A i k * Function.update p j t k)
        (∑ k : Fin 3, if k = j then A i k else 0) (p j) := by
    apply HasDerivAt.fun_sum
    intro k hk
    by_cases hkj : k = j
    · subst k
      simpa using (hasDerivAt_id (p j)).const_mul (A i j)
    · convert hasDerivAt_const (x := p j) (c := A i k * p k) using 1 <;>
        simp [hkj]
  simpa [coordinateTransform, Matrix.mulVec, dotProduct] using hs

theorem gap2 (A : Matrix (Fin 3) (Fin 3) ℝ) (q : Point3)
    (hdet : Matrix.det A ≠ 0) :
    jacobianDeterminant (coordinateTransform A⁻¹) q =
      1 / Matrix.det A := by
  rw [gap1]
  simpa [one_div] using (Matrix.det_nonsing_inv A)

theorem gap3 (A : Matrix (Fin 3) (Fin 3) ℝ) (h : Point3)
    (hdet : Matrix.det A ≠ 0) :
    coordinateTransform A '' transformedSolid A h = axisBox h := by
  classical
  have hunit : IsUnit (Matrix.det A) := isUnit_iff_ne_zero.mpr hdet
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hcomp (q : Point3) :
      coordinateTransform A (coordinateTransform A⁻¹ q) = q := by
    change A.mulVec (A⁻¹.mulVec q) = q
    calc
      A.mulVec (A⁻¹.mulVec q) = (A * A⁻¹).mulVec q :=
        Matrix.mulVec_mulVec q A A⁻¹
      _ = q := by rw [hmul]; simp
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, rfl⟩
    exact hp
  · intro q hq
    refine ⟨coordinateTransform A⁻¹ q, ?_, hcomp q⟩
    change coordinateTransform A (coordinateTransform A⁻¹ q) ∈ axisBox h
    rw [hcomp q]
    exact hq

theorem gap4 (A : Matrix (Fin 3) (Fin 3) ℝ) (h₁ h₂ h₃ : ℝ)
    (hdet : Matrix.det A ≠ 0)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hh₃ : 0 ≤ h₃) :
    volumeReal (transformedSolid A ![h₁, h₂, h₃]) =
      ∫ u in -h₁..h₁,
        ∫ v in -h₂..h₂,
          ∫ w in -h₃..h₃, 1 / |Matrix.det A| := by
  classical
  have hint :
      (∫ u in -h₁..h₁,
        ∫ v in -h₂..h₂,
          ∫ w in -h₃..h₃, 1 / |Matrix.det A|) =
        8 * h₁ * h₂ * h₃ / |Matrix.det A| := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hint]
  let L : Point3 →ₗ[ℝ] Point3 := Matrix.toLin' A
  have hLdet : LinearMap.det L ≠ 0 := by
    simpa [L] using hdet
  have hpreimage : transformedSolid A ![h₁, h₂, h₃] =
      L ⁻¹' axisBox ![h₁, h₂, h₃] := by
    rfl
  have hbox :
      axisBox ![h₁, h₂, h₃] =
        Set.pi Set.univ
          (fun i : Fin 3 =>
            Set.Icc (-(![h₁, h₂, h₃] i)) (![h₁, h₂, h₃] i)) := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      change ∀ i ∈ Set.univ,
        x i ∈ Set.Icc (-(![h₁, h₂, h₃] i)) (![h₁, h₂, h₃] i)
      intro i _
      change -(![h₁, h₂, h₃] i) ≤ x i ∧
        x i ≤ ![h₁, h₂, h₃] i
      exact hx i
    · intro hx
      change ∀ i, -(![h₁, h₂, h₃] i) ≤ x i ∧
        x i ≤ ![h₁, h₂, h₃] i
      intro i
      have hxi :
          x i ∈ Set.Icc (-(![h₁, h₂, h₃] i)) (![h₁, h₂, h₃] i) :=
        hx i (Set.mem_univ i)
      simpa only [Set.mem_Icc] using hxi
  rw [hpreimage]
  have hvol := MeasureTheory.Measure.addHaar_preimage_linearMap
    (μ := MeasureTheory.volume) hLdet (axisBox ![h₁, h₂, h₃])
  simp only [volumeReal]
  rw [hvol, hbox]
  rw [MeasureTheory.volume_pi]
  rw [MeasureTheory.Measure.pi_pi]
  all_goals
    simp [Real.volume_Icc, Fin.prod_univ_succ, L,
      hh₁, hh₂, hh₃, hdet] <;> ring

theorem gap5 (A : Matrix (Fin 3) (Fin 3) ℝ) (h₁ h₂ h₃ : ℝ)
    (hdet : Matrix.det A ≠ 0) :
    (∫ u in -h₁..h₁,
        ∫ v in -h₂..h₂,
          ∫ w in -h₃..h₃, 1 / |Matrix.det A|) =
      8 * h₁ * h₂ * h₃ / |Matrix.det A| := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem gap6 (A : Matrix (Fin 3) (Fin 3) ℝ) (h₁ h₂ h₃ : ℝ)
    (hdet : Matrix.det A ≠ 0)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) (hh₃ : 0 ≤ h₃) :
    volumeReal (transformedSolid A ![h₁, h₂, h₃]) =
      8 * h₁ * h₂ * h₃ / |Matrix.det A| := by
  calc
    volumeReal (transformedSolid A ![h₁, h₂, h₃]) =
        ∫ u in -h₁..h₁,
          ∫ v in -h₂..h₂,
            ∫ w in -h₃..h₃, 1 / |Matrix.det A| :=
      gap4 A h₁ h₂ h₃ hdet hh₁ hh₂ hh₃
    _ = 8 * h₁ * h₂ * h₃ / |Matrix.det A| := gap5 A h₁ h₂ h₃ hdet

end

end ProofGap.Exercise4127
