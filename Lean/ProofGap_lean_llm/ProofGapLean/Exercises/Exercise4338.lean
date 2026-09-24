import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4338

noncomputable section

open MeasureTheory
open scoped Interval Topology

def partialX (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => u x p.2) p.1

def partialY (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => u p.1 y) p.2

def partialXY (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialX u (p.1, y)) p.2

def L (a b c : ℝ) (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialXY u p + a * partialX u p + b * partialY u p +
    c * u p.1 p.2

def formalAdjoint
    (a b c : ℝ) (v : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialXY v p - a * partialX v p - b * partialY v p +
    c * v p.1 p.2

def P
    (b : ℝ) (u v : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 * partialX v p - b * u p.1 p.2 * v p.1 p.2

def Q
    (a : ℝ) (u v : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  v p.1 p.2 * partialY u p + a * u p.1 p.2 * v p.1 p.2

def greenCurl
    (a b : ℝ) (u v : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => Q a u v (x, p.2)) p.1 -
    deriv (fun y => P b u v (p.1, y)) p.2

def areaIntegral (f : ℝ × ℝ → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, f p

def boundaryIntegral
    (a b : ℝ) (u v : ℝ → ℝ → ℝ)
    (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    P b u v (γ t) * deriv (fun s => (γ s).1) t +
      Q a u v (γ t) * deriv (fun s => (γ s).2) t

def tangent (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (deriv (fun s => (γ s).1) t, deriv (fun s => (γ s).2) t)

def speed (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((tangent γ t).1 ^ 2 + (tangent γ t).2 ^ 2)

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

private theorem mixed_partials
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    deriv (fun x => partialY f (x, b)) a = partialXY f (a, b) := by
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
  have hm2 :=
    (partials_eq_fderiv (fun x y => partialY f (x, y)) hP2 a b).1
  have hm1 :=
    (partials_eq_fderiv (fun x y => partialX f (x, y)) hP1 a b).2
  change deriv (fun x => partialY f (x, b)) a =
    fderiv ℝ (fun p : ℝ × ℝ => partialY f p) (a, b) (1, 0) at hm2
  change deriv (fun y => partialX f (a, y)) b =
    fderiv ℝ (fun p : ℝ × ℝ => partialX f p) (a, b) (0, 1) at hm1
  rw [heq2] at hm2
  rw [heq1] at hm1
  calc
    deriv (fun x => partialY f (x, b)) a =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
      rw [hm2]
      exact fderiv_fderiv_apply _ hDfd _ _ _
    _ = fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) :=
      hf.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness]) _ _
    _ = deriv (fun y => partialX f (a, y)) b := by
      rw [hm1]
      exact (fderiv_fderiv_apply _ hDfd _ _ _).symm
    _ = partialXY f (a, b) := rfl

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

private theorem hasDerivAt_partialY_x
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    HasDerivAt (fun x => partialY f (x, b)) (partialXY f (a, b)) a := by
  have hd := (partial_maps_differentiable f hf).2
  have hline : HasFDerivAt (fun x : ℝ => (x, b))
      (ContinuousLinearMap.inl ℝ ℝ ℝ) a :=
    hasFDerivAt_prodMk_left a b
  have hs0 := (hd (a, b)).hasFDerivAt.comp a hline
  have hs : DifferentiableAt ℝ (fun x => partialY f (x, b)) a := by
    simpa [Function.comp_def] using hs0.differentiableAt
  convert hs.hasDerivAt using 1
  exact (mixed_partials f hf a b).symm

private theorem hasDerivAt_partialX_y
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    HasDerivAt (fun y => partialX f (a, y)) (partialXY f (a, b)) b := by
  have hd := (partial_maps_differentiable f hf).1
  have hline : HasFDerivAt (fun y : ℝ => (a, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) b :=
    hasFDerivAt_prodMk_right a b
  have hs0 := (hd (a, b)).hasFDerivAt.comp b hline
  have hs : DifferentiableAt ℝ (fun y => partialX f (a, y)) b := by
    simpa [Function.comp_def] using hs0.differentiableAt
  simpa [partialXY] using hs.hasDerivAt

private theorem deriv_mul_x
    (f g : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (hg : ContDiff ℝ 2 (uncurry₂ g))
    (a b : ℝ) :
    deriv (fun x => f x b * g x b) a =
      partialX f (a, b) * g a b + f a b * partialX g (a, b) := by
  exact ((hasDerivAt_x f hf a b).mul (hasDerivAt_x g hg a b)).deriv

private theorem deriv_mul_y
    (f g : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (hg : ContDiff ℝ 2 (uncurry₂ g))
    (a b : ℝ) :
    deriv (fun y => f a y * g a y) b =
      partialY f (a, b) * g a b + f a b * partialY g (a, b) := by
  exact ((hasDerivAt_y f hf a b).mul (hasDerivAt_y g hg a b)).deriv

private theorem deriv_v_partialY_x
    (u v : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (uncurry₂ u))
    (hv : ContDiff ℝ 2 (uncurry₂ v))
    (a b : ℝ) :
    deriv (fun x => v x b * partialY u (x, b)) a =
      partialX v (a, b) * partialY u (a, b) +
        v a b * partialXY u (a, b) := by
  exact ((hasDerivAt_x v hv a b).mul
    (hasDerivAt_partialY_x u hu a b)).deriv

private theorem deriv_u_partialX_y
    (u v : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (uncurry₂ u))
    (hv : ContDiff ℝ 2 (uncurry₂ v))
    (a b : ℝ) :
    deriv (fun y => u a y * partialX v (a, y)) b =
      partialY u (a, b) * partialX v (a, b) +
        u a b * partialXY v (a, b) := by
  exact ((hasDerivAt_y u hu a b).mul
    (hasDerivAt_partialX_y v hv a b)).deriv

private theorem deriv_Q_x
    (a : ℝ) (u v : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (uncurry₂ u))
    (hv : ContDiff ℝ 2 (uncurry₂ v))
    (x y : ℝ) :
    deriv (fun s => Q a u v (s, y)) x =
      (partialX v (x, y) * partialY u (x, y) +
        v x y * partialXY u (x, y)) +
      a * (partialX u (x, y) * v x y +
        u x y * partialX v (x, y)) := by
  have h₁ := (hasDerivAt_x v hv x y).mul
    (hasDerivAt_partialY_x u hu x y)
  have h₂ := ((hasDerivAt_x u hu x y).mul
    (hasDerivAt_x v hv x y)).const_mul a
  have h₂' : HasDerivAt (fun s => a * u s y * v s y)
      (a * (partialX u (x, y) * v x y +
        u x y * partialX v (x, y))) x := by
    convert h₂ using 1
    funext s
    change a * u s y * v s y = a * (u s y * v s y)
    ring
  simpa [Q] using (h₁.add h₂').deriv

private theorem deriv_P_y
    (b : ℝ) (u v : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (uncurry₂ u))
    (hv : ContDiff ℝ 2 (uncurry₂ v))
    (x y : ℝ) :
    deriv (fun s => P b u v (x, s)) y =
      (partialY u (x, y) * partialX v (x, y) +
        u x y * partialXY v (x, y)) -
      b * (partialY u (x, y) * v x y +
        u x y * partialY v (x, y)) := by
  have h₁ := (hasDerivAt_y u hu x y).mul
    (hasDerivAt_partialX_y v hv x y)
  have h₂ := ((hasDerivAt_y u hu x y).mul
    (hasDerivAt_y v hv x y)).const_mul b
  have h₂' : HasDerivAt (fun s => b * u x s * v x s)
      (b * (partialY u (x, y) * v x y +
        u x y * partialY v (x, y))) y := by
    convert h₂ using 1
    funext s
    change b * u x s * v x s = b * (u x s * v x s)
    ring
  simpa [P] using (h₁.sub h₂').deriv

theorem gap1
    (a b c : ℝ) (u v : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    v p.1 p.2 * L a b c u p -
        u p.1 p.2 * formalAdjoint a b c v p =
      v p.1 p.2 *
          (partialXY u p + a * partialX u p + b * partialY u p) -
        u p.1 p.2 *
          (partialXY v p - a * partialX v p - b * partialY v p) := by
  unfold L formalAdjoint
  ring

theorem gap2
    (a b c : ℝ) (u v : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (hu : IsC2 u) (hv : IsC2 v) :
    v p.1 p.2 * L a b c u p -
        u p.1 p.2 * formalAdjoint a b c v p =
      deriv
          (fun x =>
            v x p.2 * partialY u (x, p.2)) p.1 -
        deriv
          (fun y =>
            u p.1 y * partialX v (p.1, y)) p.2 +
        a * deriv (fun x => u x p.2 * v x p.2) p.1 +
        b * deriv (fun y => u p.1 y * v p.1 y) p.2 := by
  have hu' : ContDiff ℝ 2 (uncurry₂ u) := by
    simpa [IsC2, uncurry₂] using hu
  have hv' : ContDiff ℝ 2 (uncurry₂ v) := by
    simpa [IsC2, uncurry₂] using hv
  rw [gap1]
  rw [deriv_v_partialY_x u v hu' hv',
    deriv_u_partialX_y u v hu' hv',
    deriv_mul_x u v hu' hv', deriv_mul_y u v hu' hv']
  ring

theorem gap3
    (a b c : ℝ) (u v : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (hu : IsC2 u) (hv : IsC2 v) :
    v p.1 p.2 * L a b c u p -
        u p.1 p.2 * formalAdjoint a b c v p =
      greenCurl a b u v p := by
  have hu' : ContDiff ℝ 2 (uncurry₂ u) := by
    simpa [IsC2, uncurry₂] using hu
  have hv' : ContDiff ℝ 2 (uncurry₂ v) := by
    simpa [IsC2, uncurry₂] using hv
  rw [gap2 a b c u v p hu hv]
  unfold greenCurl
  rw [deriv_v_partialY_x u v hu' hv',
    deriv_u_partialX_y u v hu' hv',
    deriv_mul_x u v hu' hv', deriv_mul_y u v hu' hv',
    deriv_Q_x a u v hu' hv', deriv_P_y b u v hu' hv']
  ring

theorem gap4
    (a b c : ℝ) (u v : ℝ → ℝ → ℝ)
    (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hu : IsC2 u) (hv : IsC2 v)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen :
      areaIntegral (greenCurl a b u v) D =
        boundaryIntegral a b u v γ) :
    areaIntegral
        (fun p =>
          v p.1 p.2 * L a b c u p -
            u p.1 p.2 * formalAdjoint a b c v p) D =
      boundaryIntegral a b u v γ := by
  calc
    areaIntegral
        (fun p =>
          v p.1 p.2 * L a b c u p -
            u p.1 p.2 * formalAdjoint a b c v p) D =
        areaIntegral (greenCurl a b u v) D := by
      unfold areaIntegral
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => gap3 a b c u v p hu hv)
    _ = boundaryIntegral a b u v γ := hGreen

theorem gap5
    (a b c : ℝ) (u v : ℝ → ℝ → ℝ)
    (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hu : IsC2 u) (hv : IsC2 v)
    (hboundary : IsPositiveBoundary γ D)
    (hGreen :
      areaIntegral (greenCurl a b u v) D =
        boundaryIntegral a b u v γ) :
    areaIntegral
        (fun p =>
          v p.1 p.2 * L a b c u p -
            u p.1 p.2 * formalAdjoint a b c v p) D =
      ∫ t in (0 : ℝ)..1,
        P b u v (γ t) * deriv (fun s => (γ s).1) t +
          Q a u v (γ t) * deriv (fun s => (γ s).2) t := by
  calc
    areaIntegral
        (fun p =>
          v p.1 p.2 * L a b c u p -
            u p.1 p.2 * formalAdjoint a b c v p) D =
        boundaryIntegral a b u v γ :=
      gap4 a b c u v γ D hu hv hboundary hGreen
    _ = ∫ t in (0 : ℝ)..1,
        P b u v (γ t) * deriv (fun s => (γ s).1) t +
          Q a u v (γ t) * deriv (fun s => (γ s).2) t := rfl

end

end ProofGap.Exercise4338
