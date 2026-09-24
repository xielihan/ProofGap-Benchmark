import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4382

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (u v : Vec3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

structure OrientedSurface where
  parametrization : ℝ → ℝ → Vec3
  orientedAreaVector : ℝ → ℝ → Vec3
  firstLower : ℝ
  firstUpper : ℝ
  secondLower : ℝ
  secondUpper : ℝ

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  deriv (fun x => (F (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1 +
      deriv (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2

def surfaceFlux (S : OrientedSurface) (F : Vec3 → Vec3) : ℝ :=
  ∫ u in S.firstLower..S.firstUpper,
    ∫ v in S.secondLower..S.secondUpper,
      dot (S.orientedAreaVector u v) (F (S.parametrization u v))

def identityField (p : Vec3) : Vec3 :=
  p

def scalarNormalMoment (S : OrientedSurface) : ℝ :=
  ∫ u in S.firstLower..S.firstUpper,
    ∫ v in S.secondLower..S.secondUpper,
      dot (S.orientedAreaVector u v) (S.parametrization u v)

def vectorSurfaceFlux (S : OrientedSurface) : ℝ :=
  surfaceFlux S identityField

def identityDivergence (p : Vec3) : ℝ :=
  divergence identityField p

def volume (V : Set Vec3) : ℝ :=
  ∫ _p in V, (1 : ℝ)

def divergenceVolumeIntegral (V : Set Vec3) : ℝ :=
  ∫ p in V, identityDivergence p

def SatisfiesDivergenceTheorem
    (S : OrientedSurface) (V : Set Vec3) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    surfaceFlux S F = ∫ p in V, divergence F p

theorem gap1 (S : OrientedSurface) :
    scalarNormalMoment S = vectorSurfaceFlux S := by
  rfl

theorem gap2 (S : OrientedSurface) (V : Set Vec3)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    vectorSurfaceFlux S = divergenceVolumeIntegral V := by
  have hid : ContDiff ℝ 1 identityField := by
    simpa only [identityField] using
      (contDiff_id : ContDiff ℝ 1 (fun p : Vec3 => p))
  simpa only [vectorSurfaceFlux, divergenceVolumeIntegral, identityDivergence] using
    hGauss identityField hid

theorem gap3 (p : Vec3) :
    identityDivergence p = 3 := by
  norm_num [identityDivergence, divergence, identityField]

theorem gap4 (S : OrientedSurface) (V : Set Vec3)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    scalarNormalMoment S = 3 * volume V := by
  rw [gap1 S, gap2 S V hGauss]
  unfold divergenceVolumeIntegral volume
  simp_rw [gap3]
  rw [← integral_const_mul]
  norm_num

theorem gap5 (S : OrientedSurface) (V : Set Vec3)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    volume V = 1 / 3 * scalarNormalMoment S := by
  rw [gap4 S V hGauss]
  ring

theorem gap6 (S : OrientedSurface) (V : Set Vec3)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    volume V = 1 / 3 * scalarNormalMoment S := by
  exact gap5 S V hGauss

end

end ProofGap.Exercise4382
