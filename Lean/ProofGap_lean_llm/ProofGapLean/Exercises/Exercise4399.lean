import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace ProofGap.Exercise4399

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def cross (a b : Vec3) : Vec3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
    a.2.2 * b.1 - a.1 * b.2.2,
    a.1 * b.2.1 - a.2.1 * b.1)

def partialX (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

def partialY (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

def partialZ (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

def gradient (f : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX f p, partialY f p, partialZ f p)

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (F q).1) p +
    partialY (fun q => (F q).2.1) p +
      partialZ (fun q => (F q).2.2) p

structure ParametricSurface where
  param : ℝ → ℝ → Vec3
  s₀ : ℝ
  s₁ : ℝ
  t₀ : ℝ
  t₁ : ℝ

def surfacePartialS (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  (deriv (fun r => (S.param r t).1) s,
    deriv (fun r => (S.param r t).2.1) s,
    deriv (fun r => (S.param r t).2.2) s)

def surfacePartialT (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  (deriv (fun r => (S.param s r).1) t,
    deriv (fun r => (S.param s r).2.1) t,
    deriv (fun r => (S.param s r).2.2) t)

def surfaceAreaVector (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  cross (surfacePartialS S s t) (surfacePartialT S s t)

def surfaceFlux (S : ParametricSurface) (F : Vec3 → Vec3) : ℝ :=
  ∫ s in S.s₀..S.s₁,
    ∫ t in S.t₀..S.t₁,
      dot (F (S.param s t)) (surfaceAreaVector S s t)

def depth (p : Vec3) : ℝ :=
  p.2.2

def depthFieldX (p : Vec3) : Vec3 :=
  (depth p, 0, 0)

def depthFieldY (p : Vec3) : Vec3 :=
  (0, depth p, 0)

def depthFieldZ (p : Vec3) : Vec3 :=
  (0, 0, depth p)

def pressureMagnitude (ρ : ℝ) (p : Vec3) (dS : ℝ) : ℝ :=
  ρ * depth p * dS

def pressureXElement (ρ : ℝ) (normal : Vec3 → Vec3)
    (p : Vec3) (dS : ℝ) : ℝ :=
  -ρ * depth p * (normal p).1 * dS

def pressureYElement (ρ : ℝ) (normal : Vec3 → Vec3)
    (p : Vec3) (dS : ℝ) : ℝ :=
  -ρ * depth p * (normal p).2.1 * dS

def pressureZElement (ρ : ℝ) (normal : Vec3 → Vec3)
    (p : Vec3) (dS : ℝ) : ℝ :=
  -ρ * depth p * (normal p).2.2 * dS

def surfaceMomentX (S : ParametricSurface) : ℝ :=
  surfaceFlux S depthFieldX

def surfaceMomentY (S : ParametricSurface) : ℝ :=
  surfaceFlux S depthFieldY

def surfaceMomentZ (S : ParametricSurface) : ℝ :=
  surfaceFlux S depthFieldZ

def zeroVolumeIntegral (V : Set Vec3) : ℝ :=
  ∫ _p in V, (0 : ℝ)

def unitVolumeIntegral (V : Set Vec3) : ℝ :=
  ∫ _p in V, (1 : ℝ)

def volume (V : Set Vec3) : ℝ :=
  ∫ _p in V, (1 : ℝ)

def SatisfiesDivergenceTheorem
    (S : ParametricSurface) (V : Set Vec3) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    surfaceFlux S F = ∫ p in V, divergence F p

def pressureX (ρ : ℝ) (S : ParametricSurface) : ℝ :=
  -ρ * surfaceMomentX S

def pressureY (ρ : ℝ) (S : ParametricSurface) : ℝ :=
  -ρ * surfaceMomentY S

def pressureZ (ρ : ℝ) (S : ParametricSurface) : ℝ :=
  -ρ * surfaceMomentZ S

def pressureForce (ρ : ℝ) (S : ParametricSurface) : Vec3 :=
  (pressureX ρ S, pressureY ρ S, pressureZ ρ S)

def buoyancyForce (ρ : ℝ) (S : ParametricSurface) : Vec3 :=
  pressureForce ρ S

private theorem depth_contDiff : ContDiff ℝ 1 depth := by
  simpa [depth] using
    ((contDiff_snd : ContDiff ℝ 1 (Prod.snd : ℝ × ℝ → ℝ)).comp
      (contDiff_snd : ContDiff ℝ 1 (Prod.snd : Vec3 → ℝ × ℝ)))

theorem gap1 (ρ : ℝ) (p : Vec3) (dS : ℝ) :
    pressureMagnitude ρ p dS = ρ * depth p * dS := by
  rfl

theorem gap2 (ρ : ℝ) (normal : Vec3 → Vec3) (p : Vec3) (dS : ℝ) :
    pressureXElement ρ normal p dS =
      -ρ * depth p * (normal p).1 * dS := by
  rfl

theorem gap3 (ρ : ℝ) (normal : Vec3 → Vec3) (p : Vec3) (dS : ℝ) :
    pressureYElement ρ normal p dS =
      -ρ * depth p * (normal p).2.1 * dS := by
  rfl

theorem gap4 (ρ : ℝ) (normal : Vec3 → Vec3) (p : Vec3) (dS : ℝ) :
    pressureZElement ρ normal p dS =
      -ρ * depth p * (normal p).2.2 * dS := by
  rfl

theorem gap5 (ρ : ℝ) (S : ParametricSurface) :
    pressureX ρ S = -ρ * surfaceMomentX S := by
  rfl

theorem gap6 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    -ρ * surfaceMomentX S = -ρ * zeroVolumeIntegral V := by
  have hzero : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)) :=
    contDiff_const
  have hF : ContDiff ℝ 1 depthFieldX := by
    simpa [depthFieldX] using
      depth_contDiff.prodMk (hzero.prodMk hzero)
  have hflux := hGauss depthFieldX hF
  have hm : surfaceMomentX S = zeroVolumeIntegral V := by
    simpa [surfaceMomentX, zeroVolumeIntegral, divergence, partialX,
      partialY, partialZ, depthFieldX, depth] using hflux
  rw [hm]

theorem gap7 (V : Set Vec3) (ρ : ℝ) :
    -ρ * zeroVolumeIntegral V = 0 := by
  simp [zeroVolumeIntegral]

theorem gap8 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    pressureX ρ S = 0 := by
  calc
    pressureX ρ S = -ρ * surfaceMomentX S := gap5 ρ S
    _ = -ρ * zeroVolumeIntegral V := gap6 S V ρ hGauss
    _ = 0 := gap7 V ρ

theorem gap9 (ρ : ℝ) (S : ParametricSurface) :
    pressureY ρ S = -ρ * surfaceMomentY S := by
  rfl

theorem gap10 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    -ρ * surfaceMomentY S = -ρ * zeroVolumeIntegral V := by
  have hzero : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)) :=
    contDiff_const
  have hF : ContDiff ℝ 1 depthFieldY := by
    simpa [depthFieldY] using
      hzero.prodMk (depth_contDiff.prodMk hzero)
  have hflux := hGauss depthFieldY hF
  have hm : surfaceMomentY S = zeroVolumeIntegral V := by
    simpa [surfaceMomentY, zeroVolumeIntegral, divergence, partialX,
      partialY, partialZ, depthFieldY, depth] using hflux
  rw [hm]

theorem gap11 (V : Set Vec3) (ρ : ℝ) :
    -ρ * zeroVolumeIntegral V = 0 := by
  simp [zeroVolumeIntegral]

theorem gap12 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    pressureY ρ S = 0 := by
  calc
    pressureY ρ S = -ρ * surfaceMomentY S := gap9 ρ S
    _ = -ρ * zeroVolumeIntegral V := gap10 S V ρ hGauss
    _ = 0 := gap11 V ρ

theorem gap13 (ρ : ℝ) (S : ParametricSurface) :
    pressureZ ρ S = -ρ * surfaceMomentZ S := by
  rfl

theorem gap14 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    -ρ * surfaceMomentZ S = -ρ * unitVolumeIntegral V := by
  have hzero : ContDiff ℝ 1 (fun _ : Vec3 => (0 : ℝ)) :=
    contDiff_const
  have hF : ContDiff ℝ 1 depthFieldZ := by
    simpa [depthFieldZ] using
      hzero.prodMk (hzero.prodMk depth_contDiff)
  have hflux := hGauss depthFieldZ hF
  have hm : surfaceMomentZ S = unitVolumeIntegral V := by
    simpa [surfaceMomentZ, unitVolumeIntegral, divergence, partialX,
      partialY, partialZ, depthFieldZ, depth] using hflux
  rw [hm]

theorem gap15 (V : Set Vec3) (ρ : ℝ) :
    -ρ * unitVolumeIntegral V = -ρ * volume V := by
  rfl

theorem gap16 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    pressureZ ρ S = -ρ * volume V := by
  calc
    pressureZ ρ S = -ρ * surfaceMomentZ S := gap13 ρ S
    _ = -ρ * unitVolumeIntegral V := gap14 S V ρ hGauss
    _ = -ρ * volume V := gap15 V ρ

theorem gap17 (ρ : ℝ) (S : ParametricSurface) :
    buoyancyForce ρ S =
      (pressureX ρ S, pressureY ρ S, pressureZ ρ S) := by
  rfl

theorem gap18 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    (pressureX ρ S, pressureY ρ S, pressureZ ρ S) =
      (0, 0, -ρ * volume V) := by
  rw [gap8 S V ρ hGauss, gap12 S V ρ hGauss,
    gap16 S V ρ hGauss]

theorem gap19 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    buoyancyForce ρ S = (0, 0, -ρ * volume V) := by
  calc
    buoyancyForce ρ S =
        (pressureX ρ S, pressureY ρ S, pressureZ ρ S) := gap17 ρ S
    _ = (0, 0, -ρ * volume V) := gap18 S V ρ hGauss

theorem gap20 (S : ParametricSurface) (V : Set Vec3) (ρ : ℝ)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    buoyancyForce ρ S = (0, 0, -ρ * volume V) := by
  exact gap19 S V ρ hGauss

end

end ProofGap.Exercise4399
