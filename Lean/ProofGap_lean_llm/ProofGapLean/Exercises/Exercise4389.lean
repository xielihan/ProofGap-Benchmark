import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

namespace ProofGap.Exercise4389

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ
abbrev SurfaceIntegral := (Vec3 → ℝ) → ℝ

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (a : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (a q).1) p +
    partialY (fun q => (a q).2.1) p +
      partialZ (fun q => (a q).2.2) p

def transformedPoint (p : Vec3) : Vec3 :=
  (p.1 - p.2.1 + p.2.2,
    p.2.1 - p.2.2 + p.1,
    p.2.2 - p.1 + p.2.1)

def jacobianDeterminant : ℝ :=
  1 * (1 * 1 - (-1) * 1) -
    (-1) * (1 * 1 - (-1) * (-1)) +
      1 * (1 * 1 - 1 * (-1))

def octahedron : Set Vec3 :=
  {p | |p.1| + |p.2.1| + |p.2.2| ≤ 1}

def originalRegion : Set Vec3 :=
  {p | transformedPoint p ∈ octahedron}

def octahedronVolume : ℝ :=
  ∫ _p in octahedron, (1 : ℝ)

def originalRegionVolume : ℝ :=
  ∫ _p in originalRegion, (1 : ℝ)

def transformedDivergenceIntegral : ℝ :=
  ∫ _p in octahedron, (3 / 4 : ℝ)

def boundaryFlux (I : SurfaceIntegral) (normal : Vec3 → Vec3) : ℝ :=
  I (fun p => dot (transformedPoint p) (normal p))

def SatisfiesGauss (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) : Prop :=
  ∀ a : Vec3 → Vec3, ContDiff ℝ 1 a →
    I (fun p => dot (a p) (normal p)) = ∫ p in V, divergence a p

private def coordinateEquiv :
    Vec3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  { toFun := fun p => ![p.1, p.2.1, p.2.2]
    invFun := fun x => (x 0, x 1, x 2)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro x
      funext i
      fin_cases i <;> simp
    map_add' := by
      intro p q
      funext i
      fin_cases i <;> simp
    map_smul' := by
      intro r p
      funext i
      fin_cases i <;> simp }

private def transformLinear : Vec3 →ₗ[ℝ] Vec3 :=
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![(1 : ℝ), -1, 1],
      ![1, 1, -1],
      ![-1, 1, 1]]
  (coordinateEquiv.symm :
      (Fin 3 → ℝ) →ₗ[ℝ] Vec3) ∘ₗ
    Matrix.toLin' A ∘ₗ
      (coordinateEquiv :
        Vec3 →ₗ[ℝ] (Fin 3 → ℝ))

@[simp] private theorem transformLinear_apply (p : Vec3) :
    transformLinear p = transformedPoint p := by
  ext <;>
    simp [transformLinear, coordinateEquiv,
      transformedPoint, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

private theorem transformLinear_det :
    LinearMap.det transformLinear = 4 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![(1 : ℝ), -1, 1],
      ![1, 1, -1],
      ![-1, 1, 1]]
  change
    LinearMap.det
      ((coordinateEquiv.symm :
          (Fin 3 → ℝ) →ₗ[ℝ] Vec3) ∘ₗ
        Matrix.toLin' A ∘ₗ
          (coordinateEquiv :
            Vec3 →ₗ[ℝ] (Fin 3 → ℝ))) = 4
  have hconj :
      LinearMap.det
        ((coordinateEquiv.symm :
            (Fin 3 → ℝ) →ₗ[ℝ] Vec3) ∘ₗ
          Matrix.toLin' A ∘ₗ
            (coordinateEquiv :
              Vec3 →ₗ[ℝ] (Fin 3 → ℝ))) =
        LinearMap.det (Matrix.toLin' A) := by
    simpa only [LinearEquiv.symm_symm] using
      (LinearMap.det_conj
        (Matrix.toLin' A) coordinateEquiv.symm)
  rw [hconj]
  simp only [LinearMap.det_toLin']
  rw [Matrix.det_fin_three]
  norm_num [A, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

private def fin3MeasurableEquiv :
    (Fin 3 → ℝ) ≃ᵐ Vec3 :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo
        (fun _ : Fin 2 => ℝ)))

private theorem fin3MeasurableEquiv_apply
    (x : Fin 3 → ℝ) :
    fin3MeasurableEquiv x =
      (x 0, x 1, x 2) := by
  rfl

private theorem fin3MeasurableEquiv_measurePreserving :
    MeasurePreserving fin3MeasurableEquiv
      (volume : Measure (Fin 3 → ℝ))
      (volume : Measure Vec3) := by
  have hhead :=
    volume_preserving_piFinSuccAbove
      (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have htail :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.piFinTwo
            (fun _ : Fin 2 => ℝ)))
        (volume : Measure
          (ℝ × (Fin 2 → ℝ)))
        (volume : Measure Vec3) := by
    rw [Measure.volume_eq_prod,
      Measure.volume_eq_prod]
    exact
      (MeasurePreserving.id
        (volume : Measure ℝ)).prod
          (volume_preserving_piFinTwo
            (fun _ : Fin 2 => ℝ))
  simpa [fin3MeasurableEquiv,
    Function.comp_def] using htail.comp hhead

private theorem octahedron_volume :
    volume octahedron =
      ENNReal.ofReal (4 / 3 : ℝ) := by
  have hformula :=
    MeasureTheory.volume_sum_rpow_le
      (Fin 3) (p := (1 : ℝ))
        (by norm_num) 1
  have hpre :
      fin3MeasurableEquiv ⁻¹' octahedron =
        {x : Fin 3 → ℝ |
          (∑ i, |x i| ^ (1 : ℝ)) ^
            (1 / (1 : ℝ)) ≤ 1} := by
    ext x
    rw [Set.mem_preimage]
    rw [fin3MeasurableEquiv_apply]
    change
      |x 0| + |x 1| + |x 2| ≤ 1 ↔
        (∑ i, |x i| ^ (1 : ℝ)) ^
          (1 / (1 : ℝ)) ≤ 1
    simp [Fin.sum_univ_succ, add_assoc]
  have hmeasure :=
    fin3MeasurableEquiv_measurePreserving
      |>.measure_preimage_equiv octahedron
  rw [← hmeasure, hpre, hformula]
  have hG2 : Real.Gamma 2 = 1 := by
    convert Real.Gamma_nat_eq_factorial 1
      using 1 <;> norm_num
  have hG4 : Real.Gamma 4 = 6 := by
    convert Real.Gamma_nat_eq_factorial 3
      using 1 <;> norm_num
  norm_num [Fintype.card_fin, hG2, hG4]

private theorem octahedron_measurable :
    MeasurableSet octahedron := by
  unfold octahedron
  measurability

private theorem originalRegion_volume :
    volume originalRegion =
      ENNReal.ofReal (1 / 3 : ℝ) := by
  letI : Measure.IsAddHaarMeasure
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : Measure.IsAddHaarMeasure
      (volume : Measure Vec3) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hmap :
      Measure.map transformLinear volume =
        ENNReal.ofReal
          |(LinearMap.det transformLinear)⁻¹| •
            (volume : Measure Vec3) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure Vec3)
      (by rw [transformLinear_det]; norm_num)
  have heval := congrArg
    (fun μ : Measure Vec3 => μ octahedron) hmap
  change
    (Measure.map transformLinear volume) octahedron =
      (ENNReal.ofReal
        |(LinearMap.det transformLinear)⁻¹| •
          (volume : Measure Vec3)) octahedron at heval
  rw [Measure.map_apply
      transformLinear.continuous_of_finiteDimensional.measurable
      octahedron_measurable,
    Measure.smul_apply, transformLinear_det,
    octahedron_volume] at heval
  have hpre :
      transformLinear ⁻¹' octahedron =
        originalRegion := by
    ext p
    simp [originalRegion]
  rw [hpre] at heval
  rw [heval]
  rw [show |(4 : ℝ)⁻¹| =
    (1 / 4 : ℝ) by norm_num]
  simp only [smul_eq_mul]
  rw [← ENNReal.ofReal_mul
    (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  norm_num

private lemma transformedPoint_contDiff :
    ContDiff ℝ 1 transformedPoint := by
  unfold transformedPoint
  have hx : ContDiff ℝ 1 (fun p : Vec3 => p.1) := contDiff_fst
  have hy : ContDiff ℝ 1 (fun p : Vec3 => p.2.1) := contDiff_snd.fst
  have hz : ContDiff ℝ 1 (fun p : Vec3 => p.2.2) := contDiff_snd.snd
  exact ((hx.sub hy).add hz).prodMk (((hy.sub hz).add hx).prodMk ((hz.sub hx).add hy))

private lemma divergence_transformedPoint (p : Vec3) :
    divergence transformedPoint p = 3 := by
  unfold divergence partialX partialY partialZ transformedPoint
  rw [show deriv (fun x : ℝ => x - p.2.1 + p.2.2) p.1 = 1 by
        have h : HasDerivAt (fun x : ℝ => x - p.2.1 + p.2.2) 1 p.1 :=
          (hasDerivAt_id p.1).sub_const p.2.1 |>.add_const p.2.2
        exact h.deriv,
      show deriv (fun y : ℝ => y - p.2.2 + p.1) p.2.1 = 1 by
        have h : HasDerivAt (fun y : ℝ => y - p.2.2 + p.1) 1 p.2.1 :=
          (hasDerivAt_id p.2.1).sub_const p.2.2 |>.add_const p.1
        exact h.deriv,
      show deriv (fun z : ℝ => z - p.1 + p.2.1) p.2.2 = 1 by
        have h : HasDerivAt (fun z : ℝ => z - p.1 + p.2.1) 1 p.2.2 :=
          (hasDerivAt_id p.2.2).sub_const p.1 |>.add_const p.2.1
        exact h.deriv]
  norm_num

theorem gap1 (I : SurfaceIntegral) (normal : Vec3 → Vec3)
    (hGauss : SatisfiesGauss originalRegion I normal) :
    boundaryFlux I normal = 3 * originalRegionVolume := by
  rw [boundaryFlux, hGauss transformedPoint transformedPoint_contDiff]
  unfold originalRegionVolume
  simp_rw [divergence_transformedPoint]
  rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const]
  simp [mul_comm]

theorem gap2 :
    jacobianDeterminant = 4 := by
  norm_num [jacobianDeterminant]

theorem gap3 :
    octahedronVolume = 4 / 3 := by
  unfold octahedronVolume
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
    octahedron_volume]
  norm_num

theorem gap4 :
    3 * originalRegionVolume = transformedDivergenceIntegral := by
  unfold originalRegionVolume transformedDivergenceIntegral
  rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
    originalRegion_volume, octahedron_volume]
  norm_num

theorem gap5 :
    transformedDivergenceIntegral = 3 / 4 * (4 / 3) := by
  unfold transformedDivergenceIntegral
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, MeasureTheory.measureReal_def,
    octahedron_volume]
  norm_num

theorem gap6 :
    (3 / 4 : ℝ) * (4 / 3) = 1 := by
  norm_num

theorem gap7 :
    transformedDivergenceIntegral = 1 := by
  unfold transformedDivergenceIntegral
  rw [MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, MeasureTheory.measureReal_def,
    octahedron_volume]
  norm_num

end

end ProofGap.Exercise4389
