import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4442_1

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def cylinder (R h : ℝ) : Set Vec3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 ≤ R ^ 2 ∧
    0 ≤ p.2.2 ∧ p.2.2 ≤ h}

def cylinderBoundary (R h : ℝ) : Set Vec3 :=
  frontier (cylinder R h)

def vectorField (p : Vec3) : Vec3 :=
  (p.2.1 * p.2.2, p.2.2 * p.1, p.1 * p.2.1)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (F q).1) p +
    partialY (fun q => (F q).2.1) p +
      partialZ (fun q => (F q).2.2) p

def divergenceVolume (R h : ℝ) : ℝ :=
  ∫ p in cylinder R h, divergence vectorField p

def diskPoint (r φ z : ℝ) : Vec3 :=
  (r * Real.cos φ, r * Real.sin φ, z)

def sidePoint (R φ z : ℝ) : Vec3 :=
  (R * Real.cos φ, R * Real.sin φ, z)

def topNormal : Vec3 := (0, 0, 1)

def bottomNormal : Vec3 := (0, 0, -1)

def sideNormal (φ : ℝ) : Vec3 :=
  (Real.cos φ, Real.sin φ, 0)

def diskMoment (R : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..R, r ^ 3 * Real.sin φ * Real.cos φ

def topFlux (R h : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..R,
      dot (vectorField (diskPoint r φ h)) topNormal * r

def bottomFlux (R : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..R,
      dot (vectorField (diskPoint r φ 0)) bottomNormal * r

def sideFlux (R h : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ z in (0 : ℝ)..h,
      dot (vectorField (sidePoint R φ z)) (sideNormal φ) * R

def capFlux (R h : ℝ) : ℝ :=
  topFlux R h + bottomFlux R

def closedBoundaryFlux (R h : ℝ) : ℝ :=
  sideFlux R h + capFlux R h

private theorem divergence_vectorField_eq_zero (p : Vec3) :
    divergence vectorField p = 0 := by
  simp [divergence, partialX, partialY, partialZ, vectorField]

private theorem integral_sin_mul_cos :
    (∫ x in (0 : ℝ)..2 * Real.pi, Real.sin x * Real.cos x) = 0 := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ =>
        (1 / 2 : ℝ) * (Real.sin y * Real.sin y))
        (Real.sin x * Real.cos x) x := by
    convert (((Real.hasDerivAt_sin x).mul
      (Real.hasDerivAt_sin x)).const_mul (1 / 2 : ℝ)) using 1 <;> ring
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.sin x * Real.cos x) volume
      (0 : ℝ) (2 * Real.pi) :=
    (Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable _ _
  have hFTC :
      (∫ x in (0 : ℝ)..2 * Real.pi, Real.sin x * Real.cos x) =
        (1 / 2 : ℝ) *
            (Real.sin (2 * Real.pi) * Real.sin (2 * Real.pi)) -
          (1 / 2 : ℝ) * (Real.sin 0 * Real.sin 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _hx => hderiv x) hint
  simpa using hFTC

private theorem topFlux_eq_diskMoment (R h : ℝ) :
    topFlux R h = diskMoment R := by
  unfold topFlux diskMoment
  apply intervalIntegral.integral_congr
  intro φ hφ
  apply intervalIntegral.integral_congr
  intro r hr
  simp [dot, vectorField, diskPoint, topNormal] <;> ring

private theorem bottomFlux_eq_neg_diskMoment (R : ℝ) :
    bottomFlux R = -diskMoment R := by
  unfold bottomFlux diskMoment
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..R,
          dot (vectorField (diskPoint r φ 0)) bottomNormal * r) =
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..R,
            -(r ^ 3 * Real.sin φ * Real.cos φ) := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      apply intervalIntegral.integral_congr
      intro r hr
      simp [dot, vectorField, diskPoint, bottomNormal] <;> ring
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
          -(∫ r in (0 : ℝ)..R,
            r ^ 3 * Real.sin φ * Real.cos φ) := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      exact intervalIntegral.integral_neg
    _ = -(∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..R,
            r ^ 3 * Real.sin φ * Real.cos φ) := by
      exact intervalIntegral.integral_neg

private theorem sideFlux_eq_zero (R h : ℝ) :
    sideFlux R h = 0 := by
  have hpoint (φ z : ℝ) :
      dot (vectorField (sidePoint R φ z)) (sideNormal φ) * R =
        (2 * R ^ 2 * z) * (Real.sin φ * Real.cos φ) := by
    simp [dot, vectorField, sidePoint, sideNormal] <;> ring
  unfold sideFlux
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ z in (0 : ℝ)..h,
          dot (vectorField (sidePoint R φ z)) (sideNormal φ) * R) =
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          (∫ z in (0 : ℝ)..h, 2 * R ^ 2 * z) *
            (Real.sin φ * Real.cos φ) := by
      apply intervalIntegral.integral_congr
      intro φ hφ
      change
        (∫ z in (0 : ℝ)..h,
          dot (vectorField (sidePoint R φ z)) (sideNormal φ) * R) =
        (∫ z in (0 : ℝ)..h, 2 * R ^ 2 * z) *
          (Real.sin φ * Real.cos φ)
      calc
        (∫ z in (0 : ℝ)..h,
            dot (vectorField (sidePoint R φ z)) (sideNormal φ) * R) =
            ∫ z in (0 : ℝ)..h,
              (2 * R ^ 2 * z) * (Real.sin φ * Real.cos φ) := by
          apply intervalIntegral.integral_congr
          intro z hz
          exact hpoint φ z
        _ = (∫ z in (0 : ℝ)..h, 2 * R ^ 2 * z) *
              (Real.sin φ * Real.cos φ) := by
          exact intervalIntegral.integral_mul_const
            (f := fun z : ℝ => 2 * R ^ 2 * z)
            (r := Real.sin φ * Real.cos φ)
    _ = (∫ z in (0 : ℝ)..h, 2 * R ^ 2 * z) *
          (∫ φ in (0 : ℝ)..2 * Real.pi,
            Real.sin φ * Real.cos φ) := by
      exact intervalIntegral.integral_const_mul
        (r := (∫ z in (0 : ℝ)..h, 2 * R ^ 2 * z))
        (f := fun φ : ℝ => Real.sin φ * Real.cos φ)
    _ = 0 := by
      rw [integral_sin_mul_cos]
      ring

theorem gap1 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    closedBoundaryFlux R h = divergenceVolume R h := by
  simp [closedBoundaryFlux, capFlux, sideFlux_eq_zero,
    topFlux_eq_diskMoment, bottomFlux_eq_neg_diskMoment,
    divergenceVolume, divergence_vectorField_eq_zero]

theorem gap2 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    divergenceVolume R h =
      ∫ _p in cylinder R h, (0 : ℝ) := by
  simp [divergenceVolume, divergence_vectorField_eq_zero]

theorem gap3 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    (∫ _p in cylinder R h, (0 : ℝ)) = 0 := by
  simp

theorem gap4 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    closedBoundaryFlux R h = 0 := by
  calc
    closedBoundaryFlux R h = divergenceVolume R h := gap1 R h hR hh
    _ = ∫ _p in cylinder R h, (0 : ℝ) := gap2 R h hR hh
    _ = 0 := gap3 R h hR hh

theorem gap5 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    capFlux R h = topFlux R h + bottomFlux R := by
  rfl

theorem gap6 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    capFlux R h = diskMoment R - diskMoment R := by
  simp [capFlux, topFlux_eq_diskMoment, bottomFlux_eq_neg_diskMoment]

theorem gap7 (R : ℝ) (hR : 0 < R) :
    diskMoment R - diskMoment R = 0 := by
  simp

theorem gap8 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    capFlux R h = 0 := by
  calc
    capFlux R h = diskMoment R - diskMoment R := gap6 R h hR hh
    _ = 0 := gap7 R hR

theorem gap9 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    sideFlux R h = 0 := by
  exact sideFlux_eq_zero R h

end

end ProofGap.Exercise4442_1
