import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace ProofGap.Exercise4377

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ

def mixedField (p : Vec3) : Vec3 :=
  (p.2.1 * p.2.2, p.1 * p.2.2, p.1 * p.2.1)

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  deriv (fun x => (F (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1 +
    deriv (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2

def mixedDivergence (p : Vec3) : ℝ :=
  divergence mixedField p

def zeroVolumeIntegral (V : Set Vec3) : ℝ :=
  ∫ _p in V, (0 : ℝ)

abbrev BoundaryFlux := (Vec3 → Vec3) → ℝ

def SatisfiesDivergenceTheorem
    (flux : BoundaryFlux) (V : Set Vec3) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    flux F = ∫ p in V, divergence F p

private theorem mixedField_contDiff : ContDiff ℝ 1 mixedField := by
  have hx : ContDiff ℝ 1 (fun p : Vec3 => p.1) :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).contDiff
  have hy : ContDiff ℝ 1 (fun p : Vec3 => p.2.1) :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).contDiff
  have hz : ContDiff ℝ 1 (fun p : Vec3 => p.2.2) :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).contDiff
  change ContDiff ℝ 1 (fun p : Vec3 =>
    (p.2.1 * p.2.2, p.1 * p.2.2, p.1 * p.2.1))
  exact (hy.mul hz).prodMk ((hx.mul hz).prodMk (hx.mul hy))

theorem gap1 (p : Vec3) :
    mixedDivergence p = 0 := by
  simp [mixedDivergence, divergence, mixedField]

theorem gap2 (V : Set Vec3) (boundaryFlux : BoundaryFlux)
    (hGauss : SatisfiesDivergenceTheorem boundaryFlux V) :
    boundaryFlux mixedField = zeroVolumeIntegral V := by
  calc
    boundaryFlux mixedField = ∫ p in V, divergence mixedField p :=
      hGauss mixedField mixedField_contDiff
    _ = ∫ _p in V, (0 : ℝ) := by
      have hzero : divergence mixedField = fun _ : Vec3 => (0 : ℝ) := by
        funext p
        exact gap1 p
      rw [hzero]
    _ = zeroVolumeIntegral V := rfl

theorem gap3 (V : Set Vec3) :
    zeroVolumeIntegral V = 0 := by
  simp [zeroVolumeIntegral]

theorem gap4 (V : Set Vec3) (boundaryFlux : BoundaryFlux)
    (hGauss : SatisfiesDivergenceTheorem boundaryFlux V) :
    boundaryFlux mixedField = 0 := by
  calc
    boundaryFlux mixedField = zeroVolumeIntegral V := gap2 V boundaryFlux hGauss
    _ = 0 := gap3 V

end

end ProofGap.Exercise4377
