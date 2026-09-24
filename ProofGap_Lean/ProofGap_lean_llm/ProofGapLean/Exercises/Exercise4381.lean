import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4381

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def normalDot (n l : Vec3) : ℝ :=
  n.1 * l.1 + n.2.1 * l.2.1 + n.2.2 * l.2.2

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
      normalDot (S.orientedAreaVector u v) (F (S.parametrization u v))

def scalarNormalFlux (S : OrientedSurface) (l : Vec3) : ℝ :=
  ∫ u in S.firstLower..S.firstUpper,
    ∫ v in S.secondLower..S.secondUpper,
      normalDot (S.orientedAreaVector u v) l

def constantField (l : Vec3) (_p : Vec3) : Vec3 :=
  l

def vectorSurfaceFlux (S : OrientedSurface) (l : Vec3) : ℝ :=
  surfaceFlux S (constantField l)

def constantDivergence (l p : Vec3) : ℝ :=
  divergence (constantField l) p

def constantDivergenceVolumeIntegral (V : Set Vec3) (l : Vec3) : ℝ :=
  ∫ p in V, constantDivergence l p

def SatisfiesDivergenceTheorem
    (S : OrientedSurface) (V : Set Vec3) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    surfaceFlux S F = ∫ p in V, divergence F p

theorem gap1 (n l : Vec3) :
    normalDot n l =
      n.1 * l.1 + n.2.1 * l.2.1 + n.2.2 * l.2.2 := by
  rfl

theorem gap2 (S : OrientedSurface) (l : Vec3) :
    scalarNormalFlux S l = vectorSurfaceFlux S l := by
  rfl

theorem gap3 (l : Vec3) :
    ∃ lx : ℝ, lx = l.1 := by
  exact ⟨l.1, rfl⟩

theorem gap4 (l : Vec3) :
    ∃ ly : ℝ, ly = l.2.1 := by
  exact ⟨l.2.1, rfl⟩

theorem gap5 (l : Vec3) :
    ∃ lz : ℝ, lz = l.2.2 := by
  exact ⟨l.2.2, rfl⟩

theorem gap6 (S : OrientedSurface) (V : Set Vec3) (l : Vec3)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    vectorSurfaceFlux S l = constantDivergenceVolumeIntegral V l := by
  simpa [vectorSurfaceFlux, constantDivergenceVolumeIntegral,
    constantDivergence] using
    hGauss (constantField l)
      (by
        simpa [constantField] using
          (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => l)))

theorem gap7 (l p : Vec3) :
    constantDivergence l p = 0 := by
  simp [constantDivergence, divergence, constantField]

theorem gap8 (S : OrientedSurface) (V : Set Vec3) (l : Vec3)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    scalarNormalFlux S l = 0 := by
  calc
    scalarNormalFlux S l = vectorSurfaceFlux S l := gap2 S l
    _ = constantDivergenceVolumeIntegral V l := gap6 S V l hGauss
    _ = 0 := by
      simp [constantDivergenceVolumeIntegral, gap7]

theorem gap9 (S : OrientedSurface) (V : Set Vec3) (l : Vec3)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    scalarNormalFlux S l = 0 := by
  exact gap8 S V l hGauss

end

end ProofGap.Exercise4381
