import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4393_1

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

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def divergence (a : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (a q).1) p +
    partialY (fun q => (a q).2.1) p +
      partialZ (fun q => (a q).2.2) p

def normalDerivative (u : Vec3 → ℝ)
    (normal : Vec3 → Vec3) (p : Vec3) : ℝ :=
  dot (gradient u p) (normal p)

def surfaceFlux (I : SurfaceIntegral) (a normal : Vec3 → Vec3) : ℝ :=
  I (fun p => dot (a p) (normal p))

def normalBoundaryIntegral (I : SurfaceIntegral) (u : Vec3 → ℝ)
    (normal : Vec3 → Vec3) : ℝ :=
  I (normalDerivative u normal)

def gradientBoundaryFlux (I : SurfaceIntegral) (u : Vec3 → ℝ)
    (normal : Vec3 → Vec3) : ℝ :=
  surfaceFlux I (gradient u) normal

def secondDerivativeSum (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  partialX (partialX u) p + partialY (partialY u) p +
    partialZ (partialZ u) p

def laplacian (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  divergence (gradient u) p

def secondDerivativeVolume (V : Set Vec3) (u : Vec3 → ℝ) : ℝ :=
  ∫ p in V, secondDerivativeSum u p

def laplacianVolume (V : Set Vec3) (u : Vec3 → ℝ) : ℝ :=
  ∫ p in V, laplacian u p

def SatisfiesGauss (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) : Prop :=
  ∀ a : Vec3 → Vec3, ContDiff ℝ 1 a →
    surfaceFlux I a normal = ∫ p in V, divergence a p

private theorem partialX_eq_fderiv4393
    (u : Vec3 → ℝ) (hu : Differentiable ℝ u) (p : Vec3) :
    partialX u p =
      fderiv ℝ u p ((1, 0, 0) : Vec3) := by
  have hline :
      HasDerivAt (fun x : ℝ => (x, p.2.1, p.2.2))
        ((1, 0, 0) : Vec3) p.1 :=
    (hasDerivAt_id p.1).prodMk
      ((hasDerivAt_const p.1 p.2.1).prodMk
        (hasDerivAt_const p.1 p.2.2))
  have hc := (hu p).hasFDerivAt.comp p.1 hline
  have happ := congrArg
    (fun L : ℝ →L[ℝ] ℝ => L 1) hc.fderiv
  unfold partialX
  simpa [Function.comp_def, fderiv_eq_smul_deriv] using happ

private theorem partialY_eq_fderiv4393
    (u : Vec3 → ℝ) (hu : Differentiable ℝ u) (p : Vec3) :
    partialY u p =
      fderiv ℝ u p ((0, 1, 0) : Vec3) := by
  have hline :
      HasDerivAt (fun y : ℝ => (p.1, y, p.2.2))
        ((0, 1, 0) : Vec3) p.2.1 :=
    (hasDerivAt_const p.2.1 p.1).prodMk
      ((hasDerivAt_id p.2.1).prodMk
        (hasDerivAt_const p.2.1 p.2.2))
  have hc := (hu p).hasFDerivAt.comp p.2.1 hline
  have happ := congrArg
    (fun L : ℝ →L[ℝ] ℝ => L 1) hc.fderiv
  unfold partialY
  simpa [Function.comp_def, fderiv_eq_smul_deriv] using happ

private theorem partialZ_eq_fderiv4393
    (u : Vec3 → ℝ) (hu : Differentiable ℝ u) (p : Vec3) :
    partialZ u p =
      fderiv ℝ u p ((0, 0, 1) : Vec3) := by
  have hline :
      HasDerivAt (fun z : ℝ => (p.1, p.2.1, z))
        ((0, 0, 1) : Vec3) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk
        (hasDerivAt_id p.2.2))
  have hc := (hu p).hasFDerivAt.comp p.2.2 hline
  have happ := congrArg
    (fun L : ℝ →L[ℝ] ℝ => L 1) hc.fderiv
  unfold partialZ
  simpa [Function.comp_def, fderiv_eq_smul_deriv] using happ

private theorem contDiff_gradient4393
    (u : Vec3 → ℝ) (hC2 : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (gradient u) := by
  have hs : ContDiff ℝ (1 + 1) u := by
    simpa using hC2
  have hparts := contDiff_succ_iff_fderiv.mp hs
  have hu : Differentiable ℝ u := hparts.1
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) := hparts.2.2
  have hx :
      ContDiff ℝ 1
        (fun p => fderiv ℝ u p ((1, 0, 0) : Vec3)) :=
    ContDiff.continuousLinearMap_comp
      ((ContinuousLinearMap.apply ℝ ℝ) ((1, 0, 0) : Vec3)) hfd
  have hy :
      ContDiff ℝ 1
        (fun p => fderiv ℝ u p ((0, 1, 0) : Vec3)) :=
    ContDiff.continuousLinearMap_comp
      ((ContinuousLinearMap.apply ℝ ℝ) ((0, 1, 0) : Vec3)) hfd
  have hz :
      ContDiff ℝ 1
        (fun p => fderiv ℝ u p ((0, 0, 1) : Vec3)) :=
    ContDiff.continuousLinearMap_comp
      ((ContinuousLinearMap.apply ℝ ℝ) ((0, 0, 1) : Vec3)) hfd
  unfold gradient
  rw [show partialX u =
      (fun p => fderiv ℝ u p ((1, 0, 0) : Vec3)) from
        funext (partialX_eq_fderiv4393 u hu),
    show partialY u =
      (fun p => fderiv ℝ u p ((0, 1, 0) : Vec3)) from
        funext (partialY_eq_fderiv4393 u hu),
    show partialZ u =
      (fun p => fderiv ℝ u p ((0, 0, 1) : Vec3)) from
        funext (partialZ_eq_fderiv4393 u hu)]
  exact hx.prodMk (hy.prodMk hz)

theorem gap1 (u : Vec3 → ℝ) (normal : Vec3 → Vec3) (p : Vec3) :
    normalDerivative u normal p =
      (gradient u p).1 * (normal p).1 +
        (gradient u p).2.1 * (normal p).2.1 +
        (gradient u p).2.2 * (normal p).2.2 := by
  rfl

theorem gap2 (I : SurfaceIntegral) (u : Vec3 → ℝ)
    (normal : Vec3 → Vec3) :
    normalBoundaryIntegral I u normal =
      gradientBoundaryFlux I u normal := by
  rfl

theorem gap3 (V : Set Vec3) (I : SurfaceIntegral)
    (u : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (hGauss : SatisfiesGauss V I normal)
    (hC2 : ContDiff ℝ 2 u) :
    gradientBoundaryFlux I u normal = laplacianVolume V u := by
  unfold gradientBoundaryFlux laplacianVolume laplacian
  apply hGauss
  exact contDiff_gradient4393 u hC2

theorem gap4 (V : Set Vec3) (u : Vec3 → ℝ) :
    secondDerivativeVolume V u = laplacianVolume V u := by
  rfl

theorem gap5 (V : Set Vec3) (I : SurfaceIntegral)
    (u : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (hGauss : SatisfiesGauss V I normal)
    (hC2 : ContDiff ℝ 2 u) :
    normalBoundaryIntegral I u normal = laplacianVolume V u := by
  rw [gap2]
  exact gap3 V I u normal hGauss hC2

end

end ProofGap.Exercise4393_1
