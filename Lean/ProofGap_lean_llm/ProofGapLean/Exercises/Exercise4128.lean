import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4128

noncomputable section

open MeasureTheory
open scoped Matrix

abbrev Point3 := Fin 3 → ℝ

def coordinateTransform (A : Matrix (Fin 3) (Fin 3) ℝ) (p : Point3) : Point3 :=
  A.mulVec p

def coordinateJacobian
    (F : Point3 → Point3) (p : Point3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => deriv (fun t => F (Function.update p j t) i) (p j)

def jacobianDeterminant (F : Point3 → Point3) (p : Point3) : ℝ :=
  Matrix.det (coordinateJacobian F p)

def ball (h : ℝ) : Set Point3 :=
  {q | ∑ i, q i ^ 2 ≤ h ^ 2}

def transformedBall (A : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) : Set Point3 :=
  coordinateTransform A ⁻¹' ball h

def volumeReal (V : Set Point3) : ℝ :=
  (MeasureTheory.volume V).toReal

private theorem ball_eq_preimage_closedBall (h : ℝ) (hh : 0 ≤ h) :
    ball h =
      (@WithLp.toLp 2 Point3) ⁻¹'
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) h := by
  ext q
  simp only [ball, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right]
  rw [← sq_le_sq₀ (norm_nonneg (@WithLp.toLp 2 Point3 q)) hh]
  rw [EuclideanSpace.real_norm_sq_eq]

private theorem volume_ball_formula (h : ℝ) (hh : 0 ≤ h) :
    volumeReal (ball h) = 4 * Real.pi * h ^ 3 / 3 := by
  rw [ball_eq_preimage_closedBall h hh]
  unfold volumeReal
  rw [(PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet]
  rw [EuclideanSpace.volume_closedBall_fin_three]
  have hconst : 0 ≤ Real.pi * 4 / 3 := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hh,
    ENNReal.toReal_ofReal hconst]
  ring

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

theorem gap3 (A : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ)
    (hdet : Matrix.det A ≠ 0) :
    volumeReal (transformedBall A h) =
      1 / |Matrix.det A| * volumeReal (ball h) := by
  let L : Point3 →ₗ[ℝ] Point3 := Matrix.toLin' A
  have hLdet : LinearMap.det L ≠ 0 := by
    simpa [L] using hdet
  have hpreimage : transformedBall A h = L ⁻¹' ball h := by
    rfl
  rw [hpreimage]
  have hvol := MeasureTheory.Measure.addHaar_preimage_linearMap
    (μ := MeasureTheory.volume) hLdet (ball h)
  unfold volumeReal
  rw [hvol, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal]
  · simp [L, abs_inv, one_div]
  · positivity

theorem gap4 (A : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ)
    (hdet : Matrix.det A ≠ 0) (hh : 0 ≤ h) :
    1 / |Matrix.det A| * volumeReal (ball h) =
      4 * Real.pi * h ^ 3 / (3 * |Matrix.det A|) := by
  rw [volume_ball_formula h hh]
  field_simp [abs_ne_zero.mpr hdet]
  <;> ring

theorem gap5 (A : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ)
    (hdet : Matrix.det A ≠ 0) (hh : 0 ≤ h) :
    volumeReal (transformedBall A h) =
      4 * Real.pi * h ^ 3 / (3 * |Matrix.det A|) := by
  calc
    volumeReal (transformedBall A h) =
        1 / |Matrix.det A| * volumeReal (ball h) :=
      gap3 A h hdet
    _ = 4 * Real.pi * h ^ 3 / (3 * |Matrix.det A|) :=
      gap4 A h hdet hh

end

end ProofGap.Exercise4128
