import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4208

noncomputable section

open MeasureTheory

def parallelotope
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∀ i, |∑ j, A i j * x j| ≤ h i}

def coordinateBox (n : ℕ) (h : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {ξ | ∀ i, ξ i ∈ Set.Icc (-h i) (h i)}

def parallelotopeVolume
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : ℝ :=
  ∫ _x in parallelotope n A h, (1 : ℝ)

def transformedVolume
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : ℝ :=
  ∫ _ξ in coordinateBox n h, (1 / |A.det| : ℝ)

private theorem coordinateBox_eq_Icc
    (n : ℕ) (h : Fin n → ℝ) :
    coordinateBox n h = Set.Icc (fun i => -h i) h := by
  ext x
  change (∀ i, -h i ≤ x i ∧ x i ≤ h i) ↔
    (∀ i, -h i ≤ x i) ∧ ∀ i, x i ≤ h i
  constructor
  · intro hx
    exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
  · rintro ⟨hl, hu⟩ i
    exact ⟨hl i, hu i⟩

private theorem parallelotope_eq_preimage
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    parallelotope n A h =
      (Matrix.toLin' A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ⁻¹'
        coordinateBox n h := by
  ext x
  simp [parallelotope, coordinateBox, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, abs_le]

theorem gap1
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hdet : A.det ≠ 0) (hh : ∀ i, 0 ≤ h i) :
    parallelotopeVolume n A h = transformedVolume n A h := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' A
  have hLdet : LinearMap.det L ≠ 0 := by
    simpa [L, LinearMap.det_toLin'] using hdet
  rw [parallelotopeVolume, transformedVolume,
    parallelotope_eq_preimage n A h]
  simp only [MeasureTheory.setIntegral_const, one_div, smul_eq_mul,
    mul_one]
  change (MeasureTheory.volume
      ((Matrix.toLin' A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ⁻¹'
        coordinateBox n h)).toReal =
    (MeasureTheory.volume (coordinateBox n h)).toReal * |A.det|⁻¹
  change (MeasureTheory.volume (L ⁻¹' coordinateBox n h)).toReal =
    (MeasureTheory.volume (coordinateBox n h)).toReal * |A.det|⁻¹
  rw [MeasureTheory.Measure.addHaar_preimage_linearMap
    (μ := MeasureTheory.volume) hLdet (coordinateBox n h)]
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  simp [L, LinearMap.det_toLin', abs_inv, mul_comm]

theorem gap2
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hdet : A.det ≠ 0) (hh : ∀ i, 0 ≤ h i) :
    transformedVolume n A h =
      (2 : ℝ) ^ n * (∏ i, h i) / |A.det| := by
  rw [transformedVolume, MeasureTheory.setIntegral_const]
  simp only [one_div, smul_eq_mul]
  rw [coordinateBox_eq_Icc]
  change (MeasureTheory.volume (Set.Icc (fun i => -h i) h)).toReal *
      |A.det|⁻¹ =
    (2 : ℝ) ^ n * (∏ i, h i) / |A.det|
  rw [Real.volume_Icc_pi_toReal
    (fun i => by simpa using neg_nonpos.mpr (hh i))]
  have hprod :
      (∏ i : Fin n, (h i - -h i)) =
        (2 : ℝ) ^ n * ∏ i, h i := by
    calc
      (∏ i : Fin n, (h i - -h i)) =
          ∏ i : Fin n, (2 : ℝ) * h i := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
      _ = (∏ _i : Fin n, (2 : ℝ)) * ∏ i : Fin n, h i := by
        rw [Finset.prod_mul_distrib]
      _ = (2 : ℝ) ^ n * ∏ i : Fin n, h i := by simp
  rw [hprod]
  simp [div_eq_mul_inv]

theorem gap3
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hdet : A.det ≠ 0) (hh : ∀ i, 0 ≤ h i) :
    parallelotopeVolume n A h =
      (2 : ℝ) ^ n * (∏ i, h i) / |A.det| := by
  rw [gap1 n A h hdet hh, gap2 n A h hdet hh]

end

end ProofGap.Exercise4208

