import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4394

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

def laplacian (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  divergence (gradient u) p

def greenVectorField (u v : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (v p * (gradient u p).1 - u p * (gradient v p).1,
    v p * (gradient u p).2.1 - u p * (gradient v p).2.1,
    v p * (gradient u p).2.2 - u p * (gradient v p).2.2)

def greenNormalIntegrand (u v : Vec3 → ℝ)
    (normal : Vec3 → Vec3) (p : Vec3) : ℝ :=
  dot (greenVectorField u v p) (normal p)

def surfaceFlux (I : SurfaceIntegral) (a normal : Vec3 → Vec3) : ℝ :=
  I (fun p => dot (a p) (normal p))

def greenBoundaryFlux (I : SurfaceIntegral) (normal : Vec3 → Vec3)
    (u v : Vec3 → ℝ) : ℝ :=
  surfaceFlux I (greenVectorField u v) normal

def actualGreenDivergenceVolume (V : Set Vec3)
    (u v : Vec3 → ℝ) : ℝ :=
  ∫ p in V, divergence (greenVectorField u v) p

def greenDivergence (u v : Vec3 → ℝ) (p : Vec3) : ℝ :=
  v p * laplacian u p - u p * laplacian v p

def greenDivergenceVolume (V : Set Vec3)
    (u v : Vec3 → ℝ) : ℝ :=
  ∫ p in V, greenDivergence u v p

def SatisfiesGauss (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) : Prop :=
  ∀ a : Vec3 → Vec3, ContDiff ℝ 1 a →
    surfaceFlux I a normal = ∫ p in V, divergence a p

private theorem contDiff_partials (u : Vec3 → ℝ) (hU : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (partialX u) ∧
      ContDiff ℝ 1 (partialY u) ∧ ContDiff ℝ 1 (partialZ u) := by
  let familyX : Vec3 → ℝ → ℝ :=
    fun p x => u (x, p.2.1, p.2.2)
  let familyY : Vec3 → ℝ → ℝ :=
    fun p y => u (p.1, y, p.2.2)
  let familyZ : Vec3 → ℝ → ℝ :=
    fun p z => u (p.1, p.2.1, z)
  have hqP : ContDiff ℝ 2 (fun q : Vec3 × ℝ => q.1) := contDiff_fst
  have hqT : ContDiff ℝ 2 (fun q : Vec3 × ℝ => q.2) := contDiff_snd
  have hqX : ContDiff ℝ 2 (fun q : Vec3 × ℝ => q.1.1) := by
    simpa [Function.comp_def] using
      (contDiff_fst : ContDiff ℝ 2 (fun p : Vec3 => p.1)).comp hqP
  have hqYZ : ContDiff ℝ 2 (fun q : Vec3 × ℝ => q.1.2) := by
    simpa [Function.comp_def] using
      (contDiff_snd : ContDiff ℝ 2 (fun p : Vec3 => p.2)).comp hqP
  have hqY : ContDiff ℝ 2 (fun q : Vec3 × ℝ => q.1.2.1) := by
    simpa [Function.comp_def] using
      (contDiff_fst : ContDiff ℝ 2 (fun r : ℝ × ℝ => r.1)).comp hqYZ
  have hqZ : ContDiff ℝ 2 (fun q : Vec3 × ℝ => q.1.2.2) := by
    simpa [Function.comp_def] using
      (contDiff_snd : ContDiff ℝ 2 (fun r : ℝ × ℝ => r.2)).comp hqYZ
  have hfamilyX : ContDiff ℝ 2 (Function.uncurry familyX) := by
    simpa [familyX, Function.uncurry, Function.comp_def] using
      hU.comp (hqT.prodMk (hqY.prodMk hqZ))
  have hfamilyY : ContDiff ℝ 2 (Function.uncurry familyY) := by
    simpa [familyY, Function.uncurry, Function.comp_def] using
      hU.comp (hqX.prodMk (hqT.prodMk hqZ))
  have hfamilyZ : ContDiff ℝ 2 (Function.uncurry familyZ) := by
    simpa [familyZ, Function.uncurry, Function.comp_def] using
      hU.comp (hqX.prodMk (hqY.prodMk hqT))
  have hpX : ContDiff ℝ 1 (fun p : Vec3 => p.1) := contDiff_fst
  have hpYZ : ContDiff ℝ 1 (fun p : Vec3 => p.2) := contDiff_snd
  have hpY : ContDiff ℝ 1 (fun p : Vec3 => p.2.1) := by
    simpa [Function.comp_def] using
      (contDiff_fst : ContDiff ℝ 1 (fun r : ℝ × ℝ => r.1)).comp hpYZ
  have hpZ : ContDiff ℝ 1 (fun p : Vec3 => p.2.2) := by
    simpa [Function.comp_def] using
      (contDiff_snd : ContDiff ℝ 1 (fun r : ℝ × ℝ => r.2)).comp hpYZ
  have hfdX : ContDiff ℝ 1 (fun p : Vec3 =>
      fderiv ℝ (familyX p) p.1) := by
    simpa using hfamilyX.fderiv hpX (by decide)
  have hfdY : ContDiff ℝ 1 (fun p : Vec3 =>
      fderiv ℝ (familyY p) p.2.1) := by
    simpa using hfamilyY.fderiv hpY (by decide)
  have hfdZ : ContDiff ℝ 1 (fun p : Vec3 =>
      fderiv ℝ (familyZ p) p.2.2) := by
    simpa using hfamilyZ.fderiv hpZ (by decide)
  have hx : ContDiff ℝ 1 (partialX u) := by
    change ContDiff ℝ 1 (fun p : Vec3 =>
      (fderiv ℝ (familyX p) p.1) (1 : ℝ))
    exact hfdX.clm_apply
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (1 : ℝ)))
  have hy : ContDiff ℝ 1 (partialY u) := by
    change ContDiff ℝ 1 (fun p : Vec3 =>
      (fderiv ℝ (familyY p) p.2.1) (1 : ℝ))
    exact hfdY.clm_apply
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (1 : ℝ)))
  have hz : ContDiff ℝ 1 (partialZ u) := by
    change ContDiff ℝ 1 (fun p : Vec3 =>
      (fderiv ℝ (familyZ p) p.2.2) (1 : ℝ))
    exact hfdZ.clm_apply
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec3 => (1 : ℝ)))
  exact ⟨hx, hy, hz⟩

theorem gap1 (u v : Vec3 → ℝ)
    (normal : Vec3 → Vec3) (p : Vec3) :
    greenNormalIntegrand u v normal p =
      (v p * (gradient u p).1 - u p * (gradient v p).1) *
          (normal p).1 +
        (v p * (gradient u p).2.1 - u p * (gradient v p).2.1) *
          (normal p).2.1 +
        (v p * (gradient u p).2.2 - u p * (gradient v p).2.2) *
          (normal p).2.2 := by
  rfl

theorem gap2 (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) (u v : Vec3 → ℝ)
    (hGauss : SatisfiesGauss V I normal)
    (hU : ContDiff ℝ 2 u) (hV : ContDiff ℝ 2 v) :
    greenBoundaryFlux I normal u v =
      actualGreenDivergenceVolume V u v := by
  unfold greenBoundaryFlux actualGreenDivergenceVolume
  apply hGauss
  have hcu := contDiff_partials u hU
  have hcv := contDiff_partials v hV
  have hu1 : ContDiff ℝ 1 u := hU.of_le (by decide)
  have hv1 : ContDiff ℝ 1 v := hV.of_le (by decide)
  have hx : ContDiff ℝ 1 (fun p : Vec3 =>
      v p * partialX u p - u p * partialX v p) :=
    (hv1.mul hcu.1).sub (hu1.mul hcv.1)
  have hy : ContDiff ℝ 1 (fun p : Vec3 =>
      v p * partialY u p - u p * partialY v p) :=
    (hv1.mul hcu.2.1).sub (hu1.mul hcv.2.1)
  have hz : ContDiff ℝ 1 (fun p : Vec3 =>
      v p * partialZ u p - u p * partialZ v p) :=
    (hv1.mul hcu.2.2).sub (hu1.mul hcv.2.2)
  simpa [greenVectorField, gradient] using hx.prodMk (hy.prodMk hz)

theorem gap3 (V : Set Vec3) (u v : Vec3 → ℝ)
    (hU : ContDiff ℝ 2 u) (hV : ContDiff ℝ 2 v) :
    actualGreenDivergenceVolume V u v =
      greenDivergenceVolume V u v := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    have hcu := contDiff_partials u hU
    have hcv := contDiff_partials v hV
    have hu1 : ContDiff ℝ 1 u := hU.of_le (by decide)
    have hv1 : ContDiff ℝ 1 v := hV.of_le (by decide)
    have hlineX : ContDiff ℝ 1 (fun x : ℝ =>
        (x, p.2.1, p.2.2)) := by
      exact
        (contDiff_id : ContDiff ℝ 1 (fun x : ℝ => x)).prodMk
          ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => p.2.1)).prodMk
            (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => p.2.2)))
    have hlineY : ContDiff ℝ 1 (fun y : ℝ =>
        (p.1, y, p.2.2)) := by
      exact
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => p.1)).prodMk
          ((contDiff_id : ContDiff ℝ 1 (fun y : ℝ => y)).prodMk
            (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => p.2.2)))
    have hlineZ : ContDiff ℝ 1 (fun z : ℝ =>
        (p.1, p.2.1, z)) := by
      exact
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => p.1)).prodMk
          ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => p.2.1)).prodMk
            (contDiff_id : ContDiff ℝ 1 (fun z : ℝ => z)))
    have hux : HasDerivAt (fun x : ℝ => u (x, p.2.1, p.2.2))
        (partialX u p) p.1 := by
      simpa [partialX, Function.comp_def] using
        ((hu1.comp hlineX).differentiable (by decide)).differentiableAt.hasDerivAt
    have hvx : HasDerivAt (fun x : ℝ => v (x, p.2.1, p.2.2))
        (partialX v p) p.1 := by
      simpa [partialX, Function.comp_def] using
        ((hv1.comp hlineX).differentiable (by decide)).differentiableAt.hasDerivAt
    have hpux : HasDerivAt (fun x : ℝ => partialX u (x, p.2.1, p.2.2))
        (partialX (partialX u) p) p.1 := by
      simpa [partialX, Function.comp_def] using
        ((hcu.1.comp hlineX).differentiable (by decide)).differentiableAt.hasDerivAt
    have hpvx : HasDerivAt (fun x : ℝ => partialX v (x, p.2.1, p.2.2))
        (partialX (partialX v) p) p.1 := by
      simpa [partialX, Function.comp_def] using
        ((hcv.1.comp hlineX).differentiable (by decide)).differentiableAt.hasDerivAt
    have huy : HasDerivAt (fun y : ℝ => u (p.1, y, p.2.2))
        (partialY u p) p.2.1 := by
      simpa [partialY, Function.comp_def] using
        ((hu1.comp hlineY).differentiable (by decide)).differentiableAt.hasDerivAt
    have hvy : HasDerivAt (fun y : ℝ => v (p.1, y, p.2.2))
        (partialY v p) p.2.1 := by
      simpa [partialY, Function.comp_def] using
        ((hv1.comp hlineY).differentiable (by decide)).differentiableAt.hasDerivAt
    have hpuy : HasDerivAt (fun y : ℝ => partialY u (p.1, y, p.2.2))
        (partialY (partialY u) p) p.2.1 := by
      simpa [partialY, Function.comp_def] using
        ((hcu.2.1.comp hlineY).differentiable (by decide)).differentiableAt.hasDerivAt
    have hpvy : HasDerivAt (fun y : ℝ => partialY v (p.1, y, p.2.2))
        (partialY (partialY v) p) p.2.1 := by
      simpa [partialY, Function.comp_def] using
        ((hcv.2.1.comp hlineY).differentiable (by decide)).differentiableAt.hasDerivAt
    have huz : HasDerivAt (fun z : ℝ => u (p.1, p.2.1, z))
        (partialZ u p) p.2.2 := by
      simpa [partialZ, Function.comp_def] using
        ((hu1.comp hlineZ).differentiable (by decide)).differentiableAt.hasDerivAt
    have hvz : HasDerivAt (fun z : ℝ => v (p.1, p.2.1, z))
        (partialZ v p) p.2.2 := by
      simpa [partialZ, Function.comp_def] using
        ((hv1.comp hlineZ).differentiable (by decide)).differentiableAt.hasDerivAt
    have hpuz : HasDerivAt (fun z : ℝ => partialZ u (p.1, p.2.1, z))
        (partialZ (partialZ u) p) p.2.2 := by
      simpa [partialZ, Function.comp_def] using
        ((hcu.2.2.comp hlineZ).differentiable (by decide)).differentiableAt.hasDerivAt
    have hpvz : HasDerivAt (fun z : ℝ => partialZ v (p.1, p.2.1, z))
        (partialZ (partialZ v) p) p.2.2 := by
      simpa [partialZ, Function.comp_def] using
        ((hcv.2.2.comp hlineZ).differentiable (by decide)).differentiableAt.hasDerivAt
    have hdx : partialX (fun q => (greenVectorField u v q).1) p =
        partialX v p * partialX u p + v p * partialX (partialX u) p -
          (partialX u p * partialX v p + u p * partialX (partialX v) p) := by
      simpa [partialX, greenVectorField, gradient, Function.comp_def] using
        ((hvx.mul hpux).sub (hux.mul hpvx)).deriv
    have hdy : partialY (fun q => (greenVectorField u v q).2.1) p =
        partialY v p * partialY u p + v p * partialY (partialY u) p -
          (partialY u p * partialY v p + u p * partialY (partialY v) p) := by
      simpa [partialY, greenVectorField, gradient, Function.comp_def] using
        ((hvy.mul hpuy).sub (huy.mul hpvy)).deriv
    have hdz : partialZ (fun q => (greenVectorField u v q).2.2) p =
        partialZ v p * partialZ u p + v p * partialZ (partialZ u) p -
          (partialZ u p * partialZ v p + u p * partialZ (partialZ v) p) := by
      simpa [partialZ, greenVectorField, gradient, Function.comp_def] using
        ((hvz.mul hpuz).sub (huz.mul hpvz)).deriv
    unfold divergence
    rw [hdx, hdy, hdz]
    simp only [greenDivergence, laplacian, divergence, gradient]
    ring)

theorem gap4 (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) (u v : Vec3 → ℝ)
    (hGauss : SatisfiesGauss V I normal)
    (hU : ContDiff ℝ 2 u) (hV : ContDiff ℝ 2 v) :
    (∫ p in V, laplacian u p * v p - laplacian v p * u p) =
      greenBoundaryFlux I normal u v := by
  calc
    (∫ p in V, laplacian u p * v p - laplacian v p * u p) =
        greenDivergenceVolume V u v := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by
        simp only [greenDivergence]
        ring)
    _ = actualGreenDivergenceVolume V u v :=
      (gap3 V u v hU hV).symm
    _ = greenBoundaryFlux I normal u v :=
      (gap2 V I normal u v hGauss hU hV).symm

end

end ProofGap.Exercise4394
