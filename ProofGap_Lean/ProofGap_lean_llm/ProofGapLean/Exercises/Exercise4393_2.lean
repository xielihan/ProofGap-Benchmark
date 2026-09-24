import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4393_2

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

def vecNorm (a : Vec3) : ℝ :=
  Real.sqrt (a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2)

def smulVec (c : ℝ) (a : Vec3) : Vec3 :=
  (c * a.1, c * a.2.1, c * a.2.2)

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (deriv (fun x => u (x, p.2.1, p.2.2)) p.1,
    deriv (fun y => u (p.1, y, p.2.2)) p.2.1,
    deriv (fun z => u (p.1, p.2.1, z)) p.2.2)

def laplacian (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => (gradient u (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (gradient u (p.1, y, p.2.2)).2.1) p.2.1 +
    deriv (fun z => (gradient u (p.1, p.2.1, z)).2.2) p.2.2

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  deriv (fun x => (F (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1 +
    deriv (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2

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

def surfaceJacobian (S : ParametricSurface) (s t : ℝ) : ℝ :=
  vecNorm (surfaceAreaVector S s t)

def surfaceUnitNormal (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  let J := surfaceJacobian S s t
  let n := surfaceAreaVector S s t
  (n.1 / J, n.2.1 / J, n.2.2 / J)

def surfaceFlux (S : ParametricSurface) (F : Vec3 → Vec3) : ℝ :=
  ∫ s in S.s₀..S.s₁,
    ∫ t in S.t₀..S.t₁,
      dot (F (S.param s t)) (surfaceAreaVector S s t)

def normalDerivative (u : Vec3 → ℝ) (S : ParametricSurface)
    (s t : ℝ) : ℝ :=
  dot (gradient u (S.param s t)) (surfaceUnitNormal S s t)

def weightedBoundaryFlux (S : ParametricSurface) (u : Vec3 → ℝ) : ℝ :=
  ∫ s in S.s₀..S.s₁,
    ∫ t in S.t₀..S.t₁,
      u (S.param s t) * normalDerivative u S s t *
        surfaceJacobian S s t

def weightedVectorField (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  smulVec (u p) (gradient u p)

def weightedDivergence (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  divergence (weightedVectorField u) p

def weightedDivergenceVolume (V : Set Vec3) (u : Vec3 → ℝ) : ℝ :=
  ∫ p in V, weightedDivergence u p

def gradientEnergy (V : Set Vec3) (u : Vec3 → ℝ) : ℝ :=
  ∫ p in V,
    (gradient u p).1 ^ 2 + (gradient u p).2.1 ^ 2 +
      (gradient u p).2.2 ^ 2

def laplacianPairing (V : Set Vec3) (u : Vec3 → ℝ) : ℝ :=
  ∫ p in V, u p * laplacian u p

def IsC2 (u : Vec3 → ℝ) : Prop :=
  ContDiff ℝ 2 u

def SatisfiesDivergenceTheorem
    (S : ParametricSurface) (V : Set Vec3) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    surfaceFlux S F = ∫ p in V, divergence F p

private theorem derivCoordX (u : Vec3 → ℝ) (hu : Differentiable ℝ u) (p : Vec3) :
    deriv (fun x => u (x, p.2.1, p.2.2)) p.1 =
      fderiv ℝ u p ((1, 0, 0) : Vec3) := by
  have hline :
      HasDerivAt (fun x : ℝ => ((x, p.2.1, p.2.2) : Vec3))
        ((1, 0, 0) : Vec3) p.1 :=
    (hasDerivAt_id p.1).prodMk
      ((hasDerivAt_const p.1 p.2.1).prodMk
        (hasDerivAt_const p.1 p.2.2))
  simpa using
    ((hu.differentiableAt.hasFDerivAt).comp_hasDerivAt p.1 hline).deriv

private theorem derivCoordY (u : Vec3 → ℝ) (hu : Differentiable ℝ u) (p : Vec3) :
    deriv (fun y => u (p.1, y, p.2.2)) p.2.1 =
      fderiv ℝ u p ((0, 1, 0) : Vec3) := by
  have hline :
      HasDerivAt (fun y : ℝ => ((p.1, y, p.2.2) : Vec3))
        ((0, 1, 0) : Vec3) p.2.1 :=
    (hasDerivAt_const p.2.1 p.1).prodMk
      ((hasDerivAt_id p.2.1).prodMk
        (hasDerivAt_const p.2.1 p.2.2))
  simpa using
    ((hu.differentiableAt.hasFDerivAt).comp_hasDerivAt p.2.1 hline).deriv

private theorem derivCoordZ (u : Vec3 → ℝ) (hu : Differentiable ℝ u) (p : Vec3) :
    deriv (fun z => u (p.1, p.2.1, z)) p.2.2 =
      fderiv ℝ u p ((0, 0, 1) : Vec3) := by
  have hline :
      HasDerivAt (fun z : ℝ => ((p.1, p.2.1, z) : Vec3))
        ((0, 0, 1) : Vec3) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk
        (hasDerivAt_id p.2.2))
  simpa using
    ((hu.differentiableAt.hasFDerivAt).comp_hasDerivAt p.2.2 hline).deriv

private theorem contDiffGradient (u : Vec3 → ℝ) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (gradient u) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hdu : Differentiable ℝ u := hu1.differentiable (by simp)
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have hx :
      ContDiff ℝ 1 (fun p : Vec3 => fderiv ℝ u p ((1, 0, 0) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have hy :
      ContDiff ℝ 1 (fun p : Vec3 => fderiv ℝ u p ((0, 1, 0) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have hz :
      ContDiff ℝ 1 (fun p : Vec3 => fderiv ℝ u p ((0, 0, 1) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have heq :
      gradient u = fun p =>
        (fderiv ℝ u p ((1, 0, 0) : Vec3),
          fderiv ℝ u p ((0, 1, 0) : Vec3),
          fderiv ℝ u p ((0, 0, 1) : Vec3)) := by
    funext p
    simp only [gradient]
    rw [derivCoordX u hdu p, derivCoordY u hdu p, derivCoordZ u hdu p]
  rw [heq]
  exact hx.prodMk (hy.prodMk hz)

private theorem continuousGradient (u : Vec3 → ℝ) (hu : ContDiff ℝ 1 u) :
    Continuous (gradient u) := by
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hfd : ContDiff ℝ 0 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have hx :
      ContDiff ℝ 0 (fun p : Vec3 => fderiv ℝ u p ((1, 0, 0) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have hy :
      ContDiff ℝ 0 (fun p : Vec3 => fderiv ℝ u p ((0, 1, 0) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have hz :
      ContDiff ℝ 0 (fun p : Vec3 => fderiv ℝ u p ((0, 0, 1) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have heq :
      gradient u = fun p =>
        (fderiv ℝ u p ((1, 0, 0) : Vec3),
          fderiv ℝ u p ((0, 1, 0) : Vec3),
          fderiv ℝ u p ((0, 0, 1) : Vec3)) := by
    funext p
    simp only [gradient]
    rw [derivCoordX u hdu p, derivCoordY u hdu p, derivCoordZ u hdu p]
  rw [heq]
  exact (hx.prodMk (hy.prodMk hz)).continuous

private theorem contDiffWeightedVectorField (u : Vec3 → ℝ) (hu : IsC2 u) :
    ContDiff ℝ 1 (weightedVectorField u) := by
  change ContDiff ℝ 2 u at hu
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hg : ContDiff ℝ 1 (gradient u) := contDiffGradient u hu
  simpa [weightedVectorField, smulVec] using
    (hu1.mul hg.fst).prodMk
      ((hu1.mul hg.snd.fst).prodMk (hu1.mul hg.snd.snd))

private theorem weightedDivergenceIdentity (u : Vec3 → ℝ) (hu : IsC2 u)
    (p : Vec3) :
    weightedDivergence u p =
      ((gradient u p).1 ^ 2 + (gradient u p).2.1 ^ 2 +
        (gradient u p).2.2 ^ 2) + u p * laplacian u p := by
  change ContDiff ℝ 2 u at hu
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hg : ContDiff ℝ 1 (gradient u) := contDiffGradient u hu
  have hlineX : ContDiff ℝ 1
      (fun x : ℝ => ((x, p.2.1, p.2.2) : Vec3)) :=
    contDiff_id.prodMk (contDiff_const.prodMk contDiff_const)
  have hlineY : ContDiff ℝ 1
      (fun y : ℝ => ((p.1, y, p.2.2) : Vec3)) :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hlineZ : ContDiff ℝ 1
      (fun z : ℝ => ((p.1, p.2.1, z) : Vec3)) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hux : Differentiable ℝ
      (fun x : ℝ => u (x, p.2.1, p.2.2)) := by
    have hc := hu1.comp hlineX
    simpa [Function.comp_def] using hc.differentiable (by simp)
  have huy : Differentiable ℝ
      (fun y : ℝ => u (p.1, y, p.2.2)) := by
    have hc := hu1.comp hlineY
    simpa [Function.comp_def] using hc.differentiable (by simp)
  have huz : Differentiable ℝ
      (fun z : ℝ => u (p.1, p.2.1, z)) := by
    have hc := hu1.comp hlineZ
    simpa [Function.comp_def] using hc.differentiable (by simp)
  have hgx : Differentiable ℝ
      (fun x : ℝ => (gradient u (x, p.2.1, p.2.2)).1) := by
    have hc := (hg.comp hlineX).fst
    simpa [Function.comp_def] using hc.differentiable (by simp)
  have hgy : Differentiable ℝ
      (fun y : ℝ => (gradient u (p.1, y, p.2.2)).2.1) := by
    have hc := (hg.comp hlineY).snd.fst
    simpa [Function.comp_def] using hc.differentiable (by simp)
  have hgz : Differentiable ℝ
      (fun z : ℝ => (gradient u (p.1, p.2.1, z)).2.2) := by
    have hc := (hg.comp hlineZ).snd.snd
    simpa [Function.comp_def] using hc.differentiable (by simp)
  have hx0 :
      HasDerivAt (fun x : ℝ => u (x, p.2.1, p.2.2))
        (deriv (fun x : ℝ => u (x, p.2.1, p.2.2)) p.1) p.1 :=
    (hux.differentiableAt (x := p.1)).hasDerivAt
  have hy0 :
      HasDerivAt (fun y : ℝ => u (p.1, y, p.2.2))
        (deriv (fun y : ℝ => u (p.1, y, p.2.2)) p.2.1) p.2.1 :=
    (huy.differentiableAt (x := p.2.1)).hasDerivAt
  have hz0 :
      HasDerivAt (fun z : ℝ => u (p.1, p.2.1, z))
        (deriv (fun z : ℝ => u (p.1, p.2.1, z)) p.2.2) p.2.2 :=
    (huz.differentiableAt (x := p.2.2)).hasDerivAt
  have hx1 :
      HasDerivAt
        (fun x : ℝ => (gradient u (x, p.2.1, p.2.2)).1)
        (deriv (fun x : ℝ => (gradient u (x, p.2.1, p.2.2)).1) p.1) p.1 :=
    (hgx.differentiableAt (x := p.1)).hasDerivAt
  have hy1 :
      HasDerivAt
        (fun y : ℝ => (gradient u (p.1, y, p.2.2)).2.1)
        (deriv (fun y : ℝ => (gradient u (p.1, y, p.2.2)).2.1) p.2.1) p.2.1 :=
    (hgy.differentiableAt (x := p.2.1)).hasDerivAt
  have hz1 :
      HasDerivAt
        (fun z : ℝ => (gradient u (p.1, p.2.1, z)).2.2)
        (deriv (fun z : ℝ => (gradient u (p.1, p.2.1, z)).2.2) p.2.2) p.2.2 :=
    (hgz.differentiableAt (x := p.2.2)).hasDerivAt
  have hx :
      deriv (fun x => (weightedVectorField u (x, p.2.1, p.2.2)).1) p.1 =
        (gradient u p).1 ^ 2 +
          u p * deriv (fun x => (gradient u (x, p.2.1, p.2.2)).1) p.1 := by
    simpa [weightedVectorField, smulVec, gradient, pow_two] using
      (hx0.mul hx1).deriv
  have hy :
      deriv (fun y => (weightedVectorField u (p.1, y, p.2.2)).2.1) p.2.1 =
        (gradient u p).2.1 ^ 2 +
          u p * deriv (fun y => (gradient u (p.1, y, p.2.2)).2.1) p.2.1 := by
    simpa [weightedVectorField, smulVec, gradient, pow_two] using
      (hy0.mul hy1).deriv
  have hz :
      deriv (fun z => (weightedVectorField u (p.1, p.2.1, z)).2.2) p.2.2 =
        (gradient u p).2.2 ^ 2 +
          u p * deriv (fun z => (gradient u (p.1, p.2.1, z)).2.2) p.2.2 := by
    simpa [weightedVectorField, smulVec, gradient, pow_two] using
      (hz0.mul hz1).deriv
  unfold weightedDivergence divergence
  rw [hx, hy, hz]
  unfold laplacian
  ring

private theorem energyAndPairingIntegrable (V : Set Vec3) (u : Vec3 → ℝ)
    (hu : IsC2 u) (hV : Bornology.IsBounded V) :
    IntegrableOn
        (fun p => (gradient u p).1 ^ 2 + (gradient u p).2.1 ^ 2 +
          (gradient u p).2.2 ^ 2) V ∧
      IntegrableOn (fun p => u p * laplacian u p) V := by
  change ContDiff ℝ 2 u at hu
  have hg : ContDiff ℝ 1 (gradient u) := contDiffGradient u hu
  have henergy : Continuous
      (fun p => (gradient u p).1 ^ 2 + (gradient u p).2.1 ^ 2 +
        (gradient u p).2.2 ^ 2) :=
    ((hg.continuous.fst.pow 2).add (hg.continuous.snd.fst.pow 2)).add
      (hg.continuous.snd.snd.pow 2)
  have hxx : Continuous (gradient (fun p => (gradient u p).1)) :=
    continuousGradient _ hg.fst
  have hyy : Continuous (gradient (fun p => (gradient u p).2.1)) :=
    continuousGradient _ hg.snd.fst
  have hzz : Continuous (gradient (fun p => (gradient u p).2.2)) :=
    continuousGradient _ hg.snd.snd
  have hlap : Continuous (laplacian u) := by
    unfold laplacian
    exact (hxx.fst.add hyy.snd.fst).add hzz.snd.snd
  have hpair : Continuous (fun p => u p * laplacian u p) :=
    hu.continuous.mul hlap
  have hcompact : IsCompact (closure V) :=
    Metric.isCompact_iff_isClosed_bounded.2
      ⟨isClosed_closure, hV.closure⟩
  constructor
  · exact
      (henergy.continuousOn.integrableOn_compact hcompact).mono_set
        subset_closure
  · exact
      (hpair.continuousOn.integrableOn_compact hcompact).mono_set
        subset_closure

theorem gap1 (u : Vec3 → ℝ) (S : ParametricSurface) (s t : ℝ) :
    normalDerivative u S s t =
      (gradient u (S.param s t)).1 * (surfaceUnitNormal S s t).1 +
        (gradient u (S.param s t)).2.1 * (surfaceUnitNormal S s t).2.1 +
        (gradient u (S.param s t)).2.2 *
          (surfaceUnitNormal S s t).2.2 := by
  rfl

theorem gap2 (u : Vec3 → ℝ) (S : ParametricSurface)
    (hregular : ∀ s t, surfaceJacobian S s t ≠ 0) :
    weightedBoundaryFlux S u = surfaceFlux S (weightedVectorField u) := by
  unfold weightedBoundaryFlux surfaceFlux
  apply intervalIntegral.integral_congr
  intro s hs
  apply intervalIntegral.integral_congr
  intro t ht
  change
    u (S.param s t) * normalDerivative u S s t * surfaceJacobian S s t =
      dot (weightedVectorField u (S.param s t)) (surfaceAreaVector S s t)
  rw [gap1 u S s t]
  simp only [weightedVectorField, smulVec, dot, surfaceUnitNormal]
  field_simp [hregular s t]

theorem gap3 (V : Set Vec3) (S : ParametricSurface) (u : Vec3 → ℝ)
    (hu : IsC2 u) (hGauss : SatisfiesDivergenceTheorem S V) :
    surfaceFlux S (weightedVectorField u) =
      weightedDivergenceVolume V u := by
  simpa [weightedDivergenceVolume] using
    hGauss (weightedVectorField u) (contDiffWeightedVectorField u hu)

theorem gap4 (V : Set Vec3) (u : Vec3 → ℝ)
    (hu : IsC2 u) (hV : Bornology.IsBounded V) :
    weightedDivergenceVolume V u =
      gradientEnergy V u + laplacianPairing V u := by
  have hint := energyAndPairingIntegrable V u hu hV
  unfold weightedDivergenceVolume gradientEnergy laplacianPairing
  calc
    (∫ p in V, weightedDivergence u p) =
        ∫ p in V,
          ((gradient u p).1 ^ 2 + (gradient u p).2.1 ^ 2 +
              (gradient u p).2.2 ^ 2) + u p * laplacian u p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun p => weightedDivergenceIdentity u hu p)
    _ = (∫ p in V,
          (gradient u p).1 ^ 2 + (gradient u p).2.1 ^ 2 +
            (gradient u p).2.2 ^ 2) +
          ∫ p in V, u p * laplacian u p :=
      integral_add hint.1 hint.2

theorem gap5 (V : Set Vec3) (S : ParametricSurface) (u : Vec3 → ℝ)
    (hu : IsC2 u) (hV : Bornology.IsBounded V)
    (hregular : ∀ s t, surfaceJacobian S s t ≠ 0)
    (hGauss : SatisfiesDivergenceTheorem S V) :
    weightedBoundaryFlux S u =
      gradientEnergy V u + laplacianPairing V u := by
  calc
    weightedBoundaryFlux S u = surfaceFlux S (weightedVectorField u) :=
      gap2 u S hregular
    _ = weightedDivergenceVolume V u := gap3 V S u hu hGauss
    _ = gradientEnergy V u + laplacianPairing V u := gap4 V u hu hV

end

end ProofGap.Exercise4393_2
