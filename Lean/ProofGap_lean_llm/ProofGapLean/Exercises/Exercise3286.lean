import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3286

noncomputable section

def partial1 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => f t b) a

def partial2 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => f a t) b

def partial11 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f t b) a

def partial12 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial1 f a t) b

def partial21 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial2 f t b) a

def partial22 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f a t) b

def transformed (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  f (x + y) (x * y)

def uncurry₂ (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX g x t) y

def mixedRaw (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partial11 f (x + y) (x * y) +
    x * partial12 f (x + y) (x * y) +
    y * partial21 f (x + y) (x * y) +
    x * y * partial22 f (x + y) (x * y) +
    partial2 f (x + y) (x * y)

def mixedClosed (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partial11 f (x + y) (x * y) +
    (x + y) * partial12 f (x + y) (x * y) +
    x * y * partial22 f (x + y) (x * y) +
    partial2 f (x + y) (x * y)

private theorem partial1_eq_fderiv (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₂ f)) (a b : ℝ) :
    partial1 f a b =
      fderiv ℝ (uncurry₂ f) (a, b) ((1 : ℝ), (0 : ℝ)) := by
  have hpath :
      HasDerivAt (fun t : ℝ => (t, b)) ((1 : ℝ), (0 : ℝ)) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have hcomp := (hf (a, b)).hasFDerivAt.comp_hasDerivAt a hpath
  set_option maxRecDepth 4096 in
    simpa only [partial1, uncurry₂, Function.comp_apply] using hcomp.deriv

private theorem partial2_eq_fderiv (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₂ f)) (a b : ℝ) :
    partial2 f a b =
      fderiv ℝ (uncurry₂ f) (a, b) ((0 : ℝ), (1 : ℝ)) := by
  have hpath :
      HasDerivAt (fun t : ℝ => (a, t)) ((0 : ℝ), (1 : ℝ)) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have hcomp := (hf (a, b)).hasFDerivAt.comp_hasDerivAt b hpath
  set_option maxRecDepth 4096 in
    simpa only [partial2, uncurry₂, Function.comp_apply] using hcomp.deriv

private theorem contDiff_uncurry_partial1 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f)) :
    ContDiff ℝ 1 (uncurry₂ (partial1 f)) := by
  have hG : ContDiff ℝ 1 (fderiv ℝ (uncurry₂ f)) :=
    hf.fderiv_right (by decide)
  have hdir : ContDiff ℝ 1
      (fun p : ℝ × ℝ =>
        fderiv ℝ (uncurry₂ f) p ((1 : ℝ), (0 : ℝ))) :=
    hG.clm_apply contDiff_const
  have hfd : Differentiable ℝ (uncurry₂ f) := hf.differentiable (by decide)
  rw [show uncurry₂ (partial1 f) =
      (fun p : ℝ × ℝ =>
        fderiv ℝ (uncurry₂ f) p ((1 : ℝ), (0 : ℝ))) from by
        funext p
        exact partial1_eq_fderiv f hfd p.1 p.2]
  exact hdir

private theorem contDiff_uncurry_partial2 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f)) :
    ContDiff ℝ 1 (uncurry₂ (partial2 f)) := by
  have hG : ContDiff ℝ 1 (fderiv ℝ (uncurry₂ f)) :=
    hf.fderiv_right (by decide)
  have hdir : ContDiff ℝ 1
      (fun p : ℝ × ℝ =>
        fderiv ℝ (uncurry₂ f) p ((0 : ℝ), (1 : ℝ))) :=
    hG.clm_apply contDiff_const
  have hfd : Differentiable ℝ (uncurry₂ f) := hf.differentiable (by decide)
  rw [show uncurry₂ (partial2 f) =
      (fun p : ℝ × ℝ =>
        fderiv ℝ (uncurry₂ f) p ((0 : ℝ), (1 : ℝ))) from by
        funext p
        exact partial2_eq_fderiv f hfd p.1 p.2]
  exact hdir

theorem gap1 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (uncurry₂ f)) (x y : ℝ) :
    partialX (transformed f) x y =
      partial1 f (x + y) (x * y) +
        y * partial2 f (x + y) (x * y) := by
  have hfd : Differentiable ℝ (uncurry₂ f) := hf.differentiable (by decide)
  let p : ℝ × ℝ := (x + y, x * y)
  let D : (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ (uncurry₂ f) p
  have hpath : HasDerivAt (fun t : ℝ => (t + y, t * y)) ((1 : ℝ), y) x := by
    simpa only [Pi.add_apply, Pi.mul_apply, id_eq, add_zero, one_mul, mul_zero] using
      ((hasDerivAt_id x).add (hasDerivAt_const x y)).prodMk
        ((hasDerivAt_id x).mul (hasDerivAt_const x y))
  have hcomp :
      HasDerivAt (fun t : ℝ => f (t + y) (t * y)) (D ((1 : ℝ), y)) x := by
    set_option maxRecDepth 4096 in
      simpa [uncurry₂, Function.comp_def, p, D] using
        (hfd p).hasFDerivAt.comp_hasDerivAt x hpath
  have htrans : partialX (transformed f) x y = D ((1 : ℝ), y) := by
    simpa only [partialX, transformed] using hcomp.deriv
  have h1 : partial1 f (x + y) (x * y) = D ((1 : ℝ), (0 : ℝ)) := by
    simpa [p, D] using partial1_eq_fderiv f hfd (x + y) (x * y)
  have h2 : partial2 f (x + y) (x * y) = D ((0 : ℝ), (1 : ℝ)) := by
    simpa [p, D] using partial2_eq_fderiv f hfd (x + y) (x * y)
  rw [htrans, h1, h2]
  have hv :
      ((1 : ℝ), y) =
        ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp [smul_eq_mul]
  calc
    D ((1 : ℝ), y) =
        D (((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ))) :=
      congrArg D hv
    _ = D ((1 : ℝ), (0 : ℝ)) + y * D ((0 : ℝ), (1 : ℝ)) := by
      simpa only [map_add, map_smul, smul_eq_mul]

theorem gap2 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f)) (x y : ℝ) :
    partialXY (transformed f) x y = mixedRaw f x y := by
  have hf1 : ContDiff ℝ 1 (uncurry₂ f) := hf.of_le (by decide)
  have hp1 : ContDiff ℝ 1 (uncurry₂ (partial1 f)) :=
    contDiff_uncurry_partial1 f hf
  have hp2 : ContDiff ℝ 1 (uncurry₂ (partial2 f)) :=
    contDiff_uncurry_partial2 f hf
  have hpathDiff : DifferentiableAt ℝ (fun t : ℝ => (x + t, x * t)) y := by
    have hpath :
        HasDerivAt (fun t : ℝ => (x + t, x * t)) ((1 : ℝ), x) y := by
      simpa only [Pi.add_apply, Pi.mul_apply, id_eq, zero_add, zero_mul, mul_one] using
        ((hasDerivAt_const y x).add (hasDerivAt_id y)).prodMk
          ((hasDerivAt_const y x).mul (hasDerivAt_id y))
    exact hpath.differentiableAt
  have hAdiff :
      DifferentiableAt ℝ (fun t : ℝ => partial1 f (x + t) (x * t)) y := by
    change DifferentiableAt ℝ
      ((uncurry₂ (partial1 f)) ∘ fun t : ℝ => (x + t, x * t)) y
    exact ((hp1.differentiable (by decide)) (x + y, x * y)).comp y hpathDiff
  have hBdiff :
      DifferentiableAt ℝ (fun t : ℝ => partial2 f (x + t) (x * t)) y := by
    change DifferentiableAt ℝ
      ((uncurry₂ (partial2 f)) ∘ fun t : ℝ => (x + t, x * t)) y
    exact ((hp2.differentiable (by decide)) (x + y, x * y)).comp y hpathDiff
  have hAderiv :
      deriv (fun t : ℝ => partial1 f (x + t) (x * t)) y =
        partial11 f (x + y) (x * y) +
          x * partial12 f (x + y) (x * y) := by
    have h := gap1 (partial1 f) hp1 y x
    set_option maxRecDepth 4096 in
      simpa [partialX, transformed, partial1, partial2, partial11, partial12,
        Function.iterate_succ_apply, Function.iterate_zero_apply, add_comm, mul_comm] using h
  have hBderiv :
      deriv (fun t : ℝ => partial2 f (x + t) (x * t)) y =
        partial21 f (x + y) (x * y) +
          x * partial22 f (x + y) (x * y) := by
    have h := gap1 (partial2 f) hp2 y x
    set_option maxRecDepth 4096 in
      simpa [partialX, transformed, partial1, partial2, partial21, partial22,
        Function.iterate_succ_apply, Function.iterate_zero_apply, add_comm, mul_comm] using h
  have hA :
      HasDerivAt (fun t : ℝ => partial1 f (x + t) (x * t))
        (partial11 f (x + y) (x * y) +
          x * partial12 f (x + y) (x * y)) y := by
    rw [← hAderiv]
    exact hAdiff.hasDerivAt
  have hB :
      HasDerivAt (fun t : ℝ => partial2 f (x + t) (x * t))
        (partial21 f (x + y) (x * y) +
          x * partial22 f (x + y) (x * y)) y := by
    rw [← hBderiv]
    exact hBdiff.hasDerivAt
  have htotal :
      HasDerivAt
        (fun t : ℝ =>
          partial1 f (x + t) (x * t) +
            t * partial2 f (x + t) (x * t))
        ((partial11 f (x + y) (x * y) +
            x * partial12 f (x + y) (x * y)) +
          (partial2 f (x + y) (x * y) +
            y * (partial21 f (x + y) (x * y) +
              x * partial22 f (x + y) (x * y)))) y := by
    simpa only [Pi.add_apply, Pi.mul_apply, id_eq, one_mul] using
      hA.add ((hasDerivAt_id y).mul hB)
  have hpoint :
      (fun t : ℝ => partialX (transformed f) x t) =
        (fun t : ℝ =>
          partial1 f (x + t) (x * t) +
            t * partial2 f (x + t) (x * t)) := by
    funext t
    exact gap1 f hf1 x t
  unfold partialXY
  rw [hpoint, htotal.deriv]
  unfold mixedRaw
  ring

theorem gap3 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f)) (x y : ℝ) :
    mixedRaw f x y = mixedClosed f x y := by
  have hfd : Differentiable ℝ (uncurry₂ f) := hf.differentiable (by decide)
  have hp1 : ContDiff ℝ 1 (uncurry₂ (partial1 f)) :=
    contDiff_uncurry_partial1 f hf
  have hp2 : ContDiff ℝ 1 (uncurry₂ (partial2 f)) :=
    contDiff_uncurry_partial2 f hf
  let p : ℝ × ℝ := (x + y, x * y)
  let e1 : ℝ × ℝ := ((1 : ℝ), (0 : ℝ))
  let e2 : ℝ × ℝ := ((0 : ℝ), (1 : ℝ))
  have heq1 :
      uncurry₂ (partial1 f) =
        (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e1) := by
    funext q
    simpa [e1] using partial1_eq_fderiv f hfd q.1 q.2
  have heq2 :
      uncurry₂ (partial2 f) =
        (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e2) := by
    funext q
    simpa [e2] using partial2_eq_fderiv f hfd q.1 q.2
  have h12 :
      partial12 f (x + y) (x * y) =
        fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e1) p e2 := by
    calc
      partial12 f (x + y) (x * y) =
          fderiv ℝ (uncurry₂ (partial1 f)) p e2 := by
            simpa [partial12, partial2, p, e2] using
              partial2_eq_fderiv (partial1 f)
                (hp1.differentiable (by decide)) (x + y) (x * y)
      _ = _ := by rw [heq1]
  have h21 :
      partial21 f (x + y) (x * y) =
        fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e2) p e1 := by
    calc
      partial21 f (x + y) (x * y) =
          fderiv ℝ (uncurry₂ (partial2 f)) p e1 := by
            simpa [partial21, partial1, p, e1] using
              partial1_eq_fderiv (partial2 f)
                (hp2.differentiable (by decide)) (x + y) (x * y)
      _ = _ := by rw [heq2]
  have hG : ContDiff ℝ 1 (fderiv ℝ (uncurry₂ f)) :=
    hf.fderiv_right (by decide)
  have hsecond :
      HasFDerivAt (fderiv ℝ (uncurry₂ f))
        (fderiv ℝ (fderiv ℝ (uncurry₂ f)) p) p :=
    ((hG.differentiable (by decide)) p).hasFDerivAt
  have hfirst :
      ∀ᶠ q in nhds p,
        HasFDerivAt (uncurry₂ f) (fderiv ℝ (uncurry₂ f) q) q := by
    exact Filter.Eventually.of_forall (fun q => (hfd q).hasFDerivAt)
  have hsnd (u v : ℝ × ℝ) :
      fderiv ℝ (fderiv ℝ (uncurry₂ f)) p u v =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) p v u := by
    apply second_derivative_symmetric_of_eventually <;> assumption
  have hc1 : HasFDerivAt (fun _ : ℝ × ℝ => e1)
      (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    hasFDerivAt_const e1 p
  have hc2 : HasFDerivAt (fun _ : ℝ × ℝ => e2)
      (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    hasFDerivAt_const e2 p
  have hfix1 :
      fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e1) p e2 =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) p e2 e1 := by
    have h := hsecond.clm_apply hc1
    have heq := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L e2) h.fderiv
    set_option maxRecDepth 4096 in
      simpa using heq
  have hfix2 :
      fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e2) p e1 =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) p e1 e2 := by
    have h := hsecond.clm_apply hc2
    have heq := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L e1) h.fderiv
    set_option maxRecDepth 4096 in
      simpa using heq
  have hsym :
      fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e1) p e2 =
        fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ (uncurry₂ f) q e2) p e1 := by
    calc
      _ = fderiv ℝ (fderiv ℝ (uncurry₂ f)) p e2 e1 := hfix1
      _ = fderiv ℝ (fderiv ℝ (uncurry₂ f)) p e1 e2 := hsnd e2 e1
      _ = _ := hfix2.symm
  have hmixed :
      partial12 f (x + y) (x * y) = partial21 f (x + y) (x * y) :=
    h12.trans (hsym.trans h21.symm)
  unfold mixedRaw mixedClosed
  rw [hmixed]
  ring

theorem gap4 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f)) (x y : ℝ) :
    partialXY (transformed f) x y = mixedClosed f x y := by
  exact (gap2 f hf x y).trans (gap3 f hf x y)

end

end ProofGap.Exercise3286
