import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4332

noncomputable section

open MeasureTheory
open scoped Interval Topology

def partialX (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => u x p.2) p.1

def partialY (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => u p.1 y) p.2

def partialXX (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => partialX u (x, p.2)) p.1

def partialYY (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialY u (p.1, y)) p.2

def laplacian (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialXX u p + partialYY u p

def tangent (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (deriv (fun s => (γ s).1) t, deriv (fun s => (γ s).2) t)

def speed (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((tangent γ t).1 ^ 2 + (tangent γ t).2 ^ 2)

def outwardNormal (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  ((tangent γ t).2 / speed γ t, -(tangent γ t).1 / speed γ t)

def normalDerivative
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  partialX u (γ t) * (outwardNormal γ t).1 +
    partialY u (γ t) * (outwardNormal γ t).2

def weightedNormalFlux
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    u (γ t).1 (γ t).2 * normalDerivative u γ t * speed γ t

def weightedWedgeFlux
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    u (γ t).1 (γ t).2 * partialX u (γ t) *
        deriv (fun s => (γ s).2) t -
      u (γ t).1 (γ t).2 * partialY u (γ t) *
        deriv (fun s => (γ s).1) t

def areaIntegral (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, f p

def greenIntegrand (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => u x p.2 * partialX u (x, p.2)) p.1 +
    deriv (fun y => u p.1 y * partialY u (p.1, y)) p.2

def IsPositiveBoundary
    (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ContDiff ℝ 1 γ ∧
    γ 0 = γ 1 ∧
    Set.InjOn γ (Set.Ico (0 : ℝ) 1) ∧
    γ '' Set.Icc (0 : ℝ) 1 = frontier D ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t > 0) ∧
    Bornology.IsBounded D ∧
    D = closure (interior D) ∧
    0 < ∫ t in (0 : ℝ)..1,
      (γ t).1 * deriv (fun s => (γ s).2) t -
        (γ t).2 * deriv (fun s => (γ s).1) t

def IsC2 (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)

private def uncurry₂ (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2

private theorem partials_eq_fderiv
    (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (uncurry₂ f))
    (a b : ℝ) :
    partialX f (a, b) =
        fderiv ℝ (uncurry₂ f) (a, b) ((1, 0) : ℝ × ℝ) ∧
      partialY f (a, b) =
        fderiv ℝ (uncurry₂ f) (a, b) ((0, 1) : ℝ × ℝ) := by
  constructor
  · have h := (hf (a, b)).hasFDerivAt.comp a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const (x := a) (c := b)))
    simpa [partialX, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv
  · have h := (hf (a, b)).hasFDerivAt.comp b
      ((hasDerivAt_const (x := b) (c := a)).prodMk (hasDerivAt_id b))
    simpa [partialY, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv

private theorem fderiv_fderiv_apply
    (F : ℝ × ℝ → ℝ) (hDF : Differentiable ℝ (fderiv ℝ F))
    (p v w : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ F q v) p w =
      fderiv ℝ (fderiv ℝ F) p w v := by
  have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) p :=
    (hDF p).hasFDerivAt
  have hB : HasFDerivAt (fun _ : ℝ × ℝ => v)
      (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    hasFDerivAt_const (x := p) v
  have h := hA.clm_apply hB
  have heq := congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ => T w) h.fderiv
  simpa using heq

private theorem partial_maps_differentiable
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f)) :
    Differentiable ℝ (fun p : ℝ × ℝ => partialX f p) ∧
      Differentiable ℝ (fun p : ℝ × ℝ => partialY f p) := by
  have hstep := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
    (f := uncurry₂ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₂ f) := hstep.1
  have hDfd : Differentiable ℝ (fderiv ℝ (uncurry₂ f)) :=
    hstep.2.2.differentiable (by norm_num)
  have heq1 : (fun p : ℝ × ℝ => partialX f p) =
      fun p => fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ) := by
    funext p
    exact (partials_eq_fderiv f hfd p.1 p.2).1
  have heq2 : (fun p : ℝ × ℝ => partialY f p) =
      fun p => fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ) := by
    funext p
    exact (partials_eq_fderiv f hfd p.1 p.2).2
  constructor
  · rw [heq1]
    fun_prop
  · rw [heq2]
    fun_prop

private theorem hasDerivAt_x
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    HasDerivAt (fun x => f x b) (partialX f (a, b)) a := by
  have hd : Differentiable ℝ (uncurry₂ f) :=
    ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₂ f)).mp (by simpa using hf)).1
  have h := (hd (a, b)).hasFDerivAt.comp a
    ((hasDerivAt_id a).prodMk (hasDerivAt_const (x := a) (c := b)))
  rw [(partials_eq_fderiv f hd a b).1]
  simpa [uncurry₂, Function.comp_def] using h.hasDerivAt

private theorem hasDerivAt_y
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    HasDerivAt (fun y => f a y) (partialY f (a, b)) b := by
  have hd : Differentiable ℝ (uncurry₂ f) :=
    ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₂ f)).mp (by simpa using hf)).1
  have h := (hd (a, b)).hasFDerivAt.comp b
    ((hasDerivAt_const (x := b) (c := a)).prodMk (hasDerivAt_id b))
  rw [(partials_eq_fderiv f hd a b).2]
  simpa [uncurry₂, Function.comp_def] using h.hasDerivAt

private theorem hasDerivAt_partialX_x
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    HasDerivAt (fun x => partialX f (x, b)) (partialXX f (a, b)) a := by
  have hd := (partial_maps_differentiable f hf).1
  have hline : HasFDerivAt (fun x : ℝ => (x, b))
      (ContinuousLinearMap.inl ℝ ℝ ℝ) a :=
    hasFDerivAt_prodMk_left a b
  have hs := (hd (a, b)).hasFDerivAt.comp a hline
  have hdline : DifferentiableAt ℝ (fun x => partialX f (x, b)) a := by
    simpa [Function.comp_def] using hs.differentiableAt
  simpa [partialXX] using hdline.hasDerivAt

private theorem hasDerivAt_partialY_y
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    HasDerivAt (fun y => partialY f (a, y)) (partialYY f (a, b)) b := by
  have hd := (partial_maps_differentiable f hf).2
  have hline : HasFDerivAt (fun y : ℝ => (a, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) b :=
    hasFDerivAt_prodMk_right a b
  have hs := (hd (a, b)).hasFDerivAt.comp b hline
  have hdline : DifferentiableAt ℝ (fun y => partialY f (a, y)) b := by
    simpa [Function.comp_def] using hs.differentiableAt
  simpa [partialYY] using hdline.hasDerivAt

private theorem second_partials_eq_fderiv
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    partialXX f (a, b) =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) ∧
      partialYY f (a, b) =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
  have hstep := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
    (f := uncurry₂ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₂ f) := hstep.1
  have hDfd : Differentiable ℝ (fderiv ℝ (uncurry₂ f)) :=
    hstep.2.2.differentiable (by norm_num)
  have heq1 : (fun p : ℝ × ℝ => partialX f p) =
      fun p => fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ) := by
    funext p
    exact (partials_eq_fderiv f hfd p.1 p.2).1
  have heq2 : (fun p : ℝ × ℝ => partialY f p) =
      fun p => fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ) := by
    funext p
    exact (partials_eq_fderiv f hfd p.1 p.2).2
  have hP1 : Differentiable ℝ (fun p : ℝ × ℝ => partialX f p) := by
    rw [heq1]
    fun_prop
  have hP2 : Differentiable ℝ (fun p : ℝ × ℝ => partialY f p) := by
    rw [heq2]
    fun_prop
  have hm1 :=
    (partials_eq_fderiv (fun x y => partialX f (x, y)) hP1 a b).1
  have hm2 :=
    (partials_eq_fderiv (fun x y => partialY f (x, y)) hP2 a b).2
  change partialXX f (a, b) =
    fderiv ℝ (fun p : ℝ × ℝ => partialX f p) (a, b) (1, 0) at hm1
  change partialYY f (a, b) =
    fderiv ℝ (fun p : ℝ × ℝ => partialY f p) (a, b) (0, 1) at hm2
  rw [heq1] at hm1
  rw [heq2] at hm2
  constructor
  · rw [hm1]
    exact fderiv_fderiv_apply _ hDfd _ _ _
  · rw [hm2]
    exact fderiv_fderiv_apply _ hDfd _ _ _

private theorem second_partial_maps_continuous
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f)) :
    Continuous (fun p : ℝ × ℝ => partialXX f p) ∧
      Continuous (fun p : ℝ × ℝ => partialYY f p) := by
  have hstep := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
    (f := uncurry₂ f)).mp (by simpa using hf)
  have hstep₂ := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 0)
    (f := fderiv ℝ (uncurry₂ f))).mp (by simpa using hstep.2.2)
  have hDD : Continuous (fderiv ℝ (fderiv ℝ (uncurry₂ f))) :=
    contDiff_zero.mp hstep₂.2.2
  have heq1 : (fun p : ℝ × ℝ => partialXX f p) =
      fun p => fderiv ℝ (fderiv ℝ (uncurry₂ f)) p
        ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) := by
    funext p
    exact (second_partials_eq_fderiv f hf p.1 p.2).1
  have heq2 : (fun p : ℝ × ℝ => partialYY f p) =
      fun p => fderiv ℝ (fderiv ℝ (uncurry₂ f)) p
        ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
    funext p
    exact (second_partials_eq_fderiv f hf p.1 p.2).2
  constructor
  · rw [heq1]
    fun_prop
  · rw [heq2]
    fun_prop

private theorem greenIntegrand_eq_energy
    (u : ℝ → ℝ → ℝ) (hu : IsC2 u) (p : ℝ × ℝ) :
    greenIntegrand u p =
      u p.1 p.2 * laplacian u p +
        (partialX u p ^ 2 + partialY u p ^ 2) := by
  have hu' : ContDiff ℝ 2 (uncurry₂ u) := by
    simpa [IsC2, uncurry₂] using hu
  have hx := (hasDerivAt_x u hu' p.1 p.2).mul
    (hasDerivAt_partialX_x u hu' p.1 p.2)
  have hy := (hasDerivAt_y u hu' p.1 p.2).mul
    (hasDerivAt_partialY_y u hu' p.1 p.2)
  have hxd := hx.deriv
  have hyd := hy.deriv
  change deriv (fun x => u x p.2 * partialX u (x, p.2)) p.1 =
    _ at hxd
  change deriv (fun y => u p.1 y * partialY u (p.1, y)) p.2 =
    _ at hyd
  unfold greenIntegrand laplacian
  rw [hxd, hyd]
  ring

private theorem energy_integrableOn
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D) :
    IntegrableOn (fun p => u p.1 p.2 * laplacian u p) D ∧
      IntegrableOn (fun p => partialX u p ^ 2 + partialY u p ^ 2) D := by
  have hu' : ContDiff ℝ 2 (uncurry₂ u) := by
    simpa [IsC2, uncurry₂] using hu
  have hclosed : IsClosed D := by
    rw [hboundary.2.2.2.2.2.2.1]
    exact isClosed_closure
  have hcompact : IsCompact D :=
    Metric.isCompact_of_isClosed_isBounded hclosed
      hboundary.2.2.2.2.2.1
  have hU : Continuous (fun p : ℝ × ℝ => u p.1 p.2) := by
    exact ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₂ u)).mp (by simpa using hu')).1.continuous
  have hP := partial_maps_differentiable u hu'
  have hS := second_partial_maps_continuous u hu'
  have hLap : Continuous (fun p : ℝ × ℝ => laplacian u p) := by
    simpa [laplacian] using hS.1.add hS.2
  constructor
  · exact (hU.mul hLap).continuousOn.integrableOn_compact hcompact
  · exact (hP.1.continuous.pow 2 |>.add
      (hP.2.continuous.pow 2)).continuousOn.integrableOn_compact hcompact

private theorem area_green_eq_energy
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D) :
    areaIntegral (greenIntegrand u) D =
      areaIntegral (fun p => u p.1 p.2 * laplacian u p) D +
        areaIntegral (fun p => partialX u p ^ 2 + partialY u p ^ 2) D := by
  have hi := energy_integrableOn u γ D hu hboundary
  unfold areaIntegral
  calc
    (∫ p in D, greenIntegrand u p) =
        ∫ p in D,
          (u p.1 p.2 * laplacian u p) +
            (partialX u p ^ 2 + partialY u p ^ 2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun p => greenIntegrand_eq_energy u hu p)
    _ = (∫ p in D, u p.1 p.2 * laplacian u p) +
        ∫ p in D, partialX u p ^ 2 + partialY u p ^ 2 :=
      integral_add hi.1 hi.2

theorem gap1
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) :
    weightedNormalFlux u γ =
      ∫ t in (0 : ℝ)..1,
        u (γ t).1 (γ t).2 *
          (partialX u (γ t) * (outwardNormal γ t).1 +
            partialY u (γ t) * (outwardNormal γ t).2) *
          speed γ t := by
  rfl

theorem gap2
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0) :
    weightedNormalFlux u γ = weightedWedgeFlux u γ := by
  unfold weightedNormalFlux weightedWedgeFlux normalDerivative outwardNormal
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ht => by
    have ht' := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht'
    have hs : speed γ t ≠ 0 :=
      hregular t ht'
    simp only [tangent]
    field_simp
    ring)

theorem gap3
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen :
      weightedWedgeFlux u γ = areaIntegral (greenIntegrand u) D) :
    weightedWedgeFlux u γ = areaIntegral (greenIntegrand u) D := by
  exact hGreen

theorem gap4
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen :
      weightedWedgeFlux u γ = areaIntegral (greenIntegrand u) D) :
    weightedNormalFlux u γ =
      areaIntegral (fun p => u p.1 p.2 * laplacian u p) D +
        areaIntegral (fun p => partialX u p ^ 2 + partialY u p ^ 2) D := by
  have hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0 :=
    fun t ht => ne_of_gt (hboundary.2.2.2.2.1 t ht)
  calc
    weightedNormalFlux u γ = weightedWedgeFlux u γ :=
      gap2 u γ hregular
    _ = areaIntegral (greenIntegrand u) D := hGreen
    _ = areaIntegral (fun p => u p.1 p.2 * laplacian u p) D +
        areaIntegral (fun p => partialX u p ^ 2 + partialY u p ^ 2) D :=
      area_green_eq_energy u γ D hu hboundary

theorem gap5
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen :
      weightedWedgeFlux u γ = areaIntegral (greenIntegrand u) D) :
    areaIntegral (fun p => partialX u p ^ 2 + partialY u p ^ 2) D =
      -areaIntegral (fun p => u p.1 p.2 * laplacian u p) D +
        weightedNormalFlux u γ := by
  rw [gap4 u γ D hu hboundary hGreen]
  ring

theorem gap6
    (u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen :
      weightedWedgeFlux u γ = areaIntegral (greenIntegrand u) D) :
    areaIntegral (fun p => partialX u p ^ 2 + partialY u p ^ 2) D =
      weightedNormalFlux u γ -
        areaIntegral (fun p => u p.1 p.2 * laplacian u p) D := by
  rw [gap4 u γ D hu hboundary hGreen]
  ring

end

end ProofGap.Exercise4332
