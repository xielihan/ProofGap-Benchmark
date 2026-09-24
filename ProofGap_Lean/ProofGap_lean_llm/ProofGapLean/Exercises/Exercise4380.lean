import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4380

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ
abbrev BoundaryFlux := (Vec3 → Vec3) → ℝ

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  deriv (fun x => (F (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1 +
    deriv (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2

def SatisfiesDivergenceTheorem
    (flux : BoundaryFlux) (V : Set Vec3) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    flux F = ∫ p in V, divergence F p

def curlDivergence
    (Ryx Qzx Pzy Rxy Qxz Pyz : ℝ) : ℝ :=
  Ryx - Qzx + Pzy - Rxy + Qxz - Pyz

def zeroVolumeIntegral (V : Set Vec3) : ℝ :=
  ∫ _p in V, (0 : ℝ)

theorem gap1 (Ryx Qzx Pzy Rxy Qxz Pyz : ℝ)
    (hR : Ryx = Rxy) (hQ : Qzx = Qxz) (hP : Pzy = Pyz) :
    curlDivergence Ryx Qzx Pzy Rxy Qxz Pyz = 0 := by
  unfold curlDivergence
  rw [hR, hQ, hP]
  ring

theorem gap2 (V : Set Vec3) (curlField : Vec3 → Vec3)
    (curlBoundaryFlux : BoundaryFlux)
    (hC1 : ContDiff ℝ 1 curlField)
    (hDivZero : ∀ p, divergence curlField p = 0)
    (hGauss : SatisfiesDivergenceTheorem curlBoundaryFlux V) :
    curlBoundaryFlux curlField = zeroVolumeIntegral V := by
  calc
    curlBoundaryFlux curlField = ∫ p in V, divergence curlField p :=
      hGauss curlField hC1
    _ = zeroVolumeIntegral V := by
      simp [zeroVolumeIntegral, hDivZero]

theorem gap3 (V : Set Vec3) :
    zeroVolumeIntegral V = 0 := by
  simp [zeroVolumeIntegral]

theorem gap4 (V : Set Vec3) (curlField : Vec3 → Vec3)
    (curlBoundaryFlux : BoundaryFlux)
    (hC1 : ContDiff ℝ 1 curlField)
    (hDivZero : ∀ p, divergence curlField p = 0)
    (hGauss : SatisfiesDivergenceTheorem curlBoundaryFlux V) :
    curlBoundaryFlux curlField = 0 := by
  calc
    curlBoundaryFlux curlField = zeroVolumeIntegral V :=
      gap2 V curlField curlBoundaryFlux hC1 hDivZero hGauss
    _ = 0 := gap3 V

theorem gap5 (V : Set Vec3) (curlField : Vec3 → Vec3)
    (curlBoundaryFlux : BoundaryFlux) (expandedCurlFlux : ℝ)
    (hC1 : ContDiff ℝ 1 curlField)
    (hDivZero : ∀ p, divergence curlField p = 0)
    (hExpand : expandedCurlFlux = curlBoundaryFlux curlField)
    (hGauss : SatisfiesDivergenceTheorem curlBoundaryFlux V) :
    expandedCurlFlux = 0 := by
  calc
    expandedCurlFlux = curlBoundaryFlux curlField := hExpand
    _ = 0 := gap4 V curlField curlBoundaryFlux hC1 hDivZero hGauss

end

end ProofGap.Exercise4380
