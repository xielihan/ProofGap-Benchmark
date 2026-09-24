import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4334

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
    (weight u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    weight (γ t).1 (γ t).2 * normalDerivative u γ t * speed γ t

def weightedWedgeFlux
    (weight u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    weight (γ t).1 (γ t).2 * partialX u (γ t) *
        deriv (fun s => (γ s).2) t -
      weight (γ t).1 (γ t).2 * partialY u (γ t) *
        deriv (fun s => (γ s).1) t

def areaIntegral (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, f p

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

private theorem laplacian_continuous
    (f : ℝ → ℝ → ℝ) (hf : IsC2 f) :
    Continuous (fun p : ℝ × ℝ => laplacian f p) := by
  have hf' : ContDiff ℝ 2 (uncurry₂ f) := by
    simpa [IsC2, uncurry₂] using hf
  have hstep := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
    (f := uncurry₂ f)).mp (by simpa using hf')
  have hstep₂ := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 0)
    (f := fderiv ℝ (uncurry₂ f))).mp (by simpa using hstep.2.2)
  have hDD : Continuous (fderiv ℝ (fderiv ℝ (uncurry₂ f))) :=
    contDiff_zero.mp hstep₂.2.2
  have hXX : Continuous (fun p : ℝ × ℝ => partialXX f p) := by
    have heq : (fun p : ℝ × ℝ => partialXX f p) =
        fun p => fderiv ℝ (fderiv ℝ (uncurry₂ f)) p
          ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) := by
      funext p
      exact (second_partials_eq_fderiv f hf' p.1 p.2).1
    rw [heq]
    fun_prop
  have hYY : Continuous (fun p : ℝ × ℝ => partialYY f p) := by
    have heq : (fun p : ℝ × ℝ => partialYY f p) =
        fun p => fderiv ℝ (fderiv ℝ (uncurry₂ f)) p
          ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
      funext p
      exact (second_partials_eq_fderiv f hf' p.1 p.2).2
    rw [heq]
    fun_prop
  simpa [laplacian] using hXX.add hYY

private theorem c2_continuous
    (f : ℝ → ℝ → ℝ) (hf : IsC2 f) :
    Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
  have hf' : ContDiff ℝ 2 (uncurry₂ f) := by
    simpa [IsC2, uncurry₂] using hf
  have hd : Differentiable ℝ (uncurry₂ f) :=
    ((contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₂ f)).mp (by simpa using hf')).1
  exact hd.continuous

private theorem weighted_laplacian_integrableOn
    (weight u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hw : IsC2 weight) (hu : IsC2 u)
    (hboundary : IsPositiveBoundary γ D) :
    IntegrableOn (fun p => weight p.1 p.2 * laplacian u p) D := by
  have hclosed : IsClosed D := by
    rw [hboundary.2.2.2.2.2.2.1]
    exact isClosed_closure
  have hcompact : IsCompact D :=
    Metric.isCompact_of_isClosed_isBounded hclosed
      hboundary.2.2.2.2.2.1
  exact ((c2_continuous weight hw).mul
    (laplacian_continuous u hu)).continuousOn.integrableOn_compact hcompact

private theorem normalFlux_eq_wedgeFlux
    (weight u : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0) :
    weightedNormalFlux weight u γ = weightedWedgeFlux weight u γ := by
  unfold weightedNormalFlux weightedWedgeFlux normalDerivative outwardNormal
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ht => by
    have ht' := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht'
    have hs : speed γ t ≠ 0 := hregular t ht'
    simp only [tangent]
    field_simp
    ring)

theorem gap1
    (u v : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0) :
    weightedNormalFlux v u γ = weightedWedgeFlux v u γ := by
  exact normalFlux_eq_wedgeFlux v u γ hregular

theorem gap2
    (u v : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u) (hv : IsC2 v)
    (hboundary : IsPositiveBoundary γ D)
    (hGreenVU :
      weightedWedgeFlux v u γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => v p.1 p.2 * laplacian u p) D) :
    weightedNormalFlux v u γ =
      areaIntegral
        (fun p =>
          partialX u p * partialX v p +
            partialY u p * partialY v p) D +
      areaIntegral (fun p => v p.1 p.2 * laplacian u p) D := by
  have hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0 :=
    fun t ht => ne_of_gt (hboundary.2.2.2.2.1 t ht)
  exact (gap1 u v γ hregular).trans hGreenVU

theorem gap3
    (u v : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0) :
    weightedNormalFlux u v γ = weightedWedgeFlux u v γ := by
  exact normalFlux_eq_wedgeFlux u v γ hregular

theorem gap4
    (u v : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u) (hv : IsC2 v)
    (hboundary : IsPositiveBoundary γ D)
    (hGreenUV :
      weightedWedgeFlux u v γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => u p.1 p.2 * laplacian v p) D) :
    weightedNormalFlux u v γ =
      areaIntegral
        (fun p =>
          partialX u p * partialX v p +
            partialY u p * partialY v p) D +
      areaIntegral (fun p => u p.1 p.2 * laplacian v p) D := by
  have hregular : ∀ t ∈ Set.Icc (0 : ℝ) 1, speed γ t ≠ 0 :=
    fun t ht => ne_of_gt (hboundary.2.2.2.2.1 t ht)
  exact (gap3 u v γ hregular).trans hGreenUV

theorem gap5
    (u v : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u) (hv : IsC2 v)
    (hboundary : IsPositiveBoundary γ D)
    (hGreenVU :
      weightedWedgeFlux v u γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => v p.1 p.2 * laplacian u p) D)
    (hGreenUV :
      weightedWedgeFlux u v γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => u p.1 p.2 * laplacian v p) D) :
    weightedNormalFlux v u γ - weightedNormalFlux u v γ =
      areaIntegral (fun p => v p.1 p.2 * laplacian u p) D -
        areaIntegral (fun p => u p.1 p.2 * laplacian v p) D := by
  rw [gap2 u v γ D hu hv hboundary hGreenVU,
    gap4 u v γ D hu hv hboundary hGreenUV]
  ring

theorem gap6
    (u v : ℝ → ℝ → ℝ) (D : Set (ℝ × ℝ))
    (hvu : IntegrableOn (fun p => v p.1 p.2 * laplacian u p) D)
    (huv : IntegrableOn (fun p => u p.1 p.2 * laplacian v p) D) :
    areaIntegral (fun p => v p.1 p.2 * laplacian u p) D -
        areaIntegral (fun p => u p.1 p.2 * laplacian v p) D =
      areaIntegral
        (fun p =>
          v p.1 p.2 * laplacian u p -
            u p.1 p.2 * laplacian v p) D := by
  unfold areaIntegral
  exact (integral_sub hvu huv).symm

theorem gap7
    (u v : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u) (hv : IsC2 v)
    (hboundary : IsPositiveBoundary γ D)
    (hGreenVU :
      weightedWedgeFlux v u γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => v p.1 p.2 * laplacian u p) D)
    (hGreenUV :
      weightedWedgeFlux u v γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => u p.1 p.2 * laplacian v p) D) :
    weightedNormalFlux v u γ - weightedNormalFlux u v γ =
      areaIntegral
        (fun p =>
          v p.1 p.2 * laplacian u p -
            u p.1 p.2 * laplacian v p) D := by
  have hvu := weighted_laplacian_integrableOn v u γ D hv hu hboundary
  have huv := weighted_laplacian_integrableOn u v γ D hu hv hboundary
  calc
    weightedNormalFlux v u γ - weightedNormalFlux u v γ =
        areaIntegral (fun p => v p.1 p.2 * laplacian u p) D -
          areaIntegral (fun p => u p.1 p.2 * laplacian v p) D :=
      gap5 u v γ D hu hv hboundary hGreenVU hGreenUV
    _ = areaIntegral
        (fun p =>
          v p.1 p.2 * laplacian u p -
            u p.1 p.2 * laplacian v p) D :=
      gap6 u v D hvu huv

theorem gap8
    (u v : ℝ → ℝ → ℝ) (γ : ℝ → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (hu : IsC2 u) (hv : IsC2 v)
    (hboundary : IsPositiveBoundary γ D)
    (hGreenVU :
      weightedWedgeFlux v u γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => v p.1 p.2 * laplacian u p) D)
    (hGreenUV :
      weightedWedgeFlux u v γ =
        areaIntegral
          (fun p =>
            partialX u p * partialX v p +
              partialY u p * partialY v p) D +
        areaIntegral (fun p => u p.1 p.2 * laplacian v p) D) :
    areaIntegral
        (fun p =>
          v p.1 p.2 * laplacian u p -
            u p.1 p.2 * laplacian v p) D =
      weightedNormalFlux v u γ - weightedNormalFlux u v γ := by
  exact (gap7 u v γ D hu hv hboundary hGreenVU hGreenUV).symm

end

end ProofGap.Exercise4334
