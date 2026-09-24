import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3439

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def dydx (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 y t / d1 x t

def d2ydx2 (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 (dydx x y) t / d1 x t

theorem gap1 (x y : ℝ → ℝ) (t : ℝ)
    (hRegular : d1 x t ≠ 0) :
    dydx x y t = d1 y t / d1 x t := by
  rfl

theorem gap2 (x y u : ℝ → ℝ)
    (hX : ∀ t, x t = Real.exp t)
    (hY : ∀ t, y t = u t * Real.exp (2 * t))
    (hu : ContDiff ℝ 1 u) :
    ∀ t,
      d1 y t / d1 x t =
        Real.exp (2 * t) * (2 * u t + d1 u t) /
          Real.exp t := by
  intro t
  have hx : x = fun s : ℝ => Real.exp s := funext hX
  have hy : y = fun s : ℝ => u s * Real.exp (2 * s) := funext hY
  rw [hx, hy]
  unfold d1
  have huDiff : Differentiable ℝ u :=
    hu.differentiable (by decide)
  have huDeriv : HasDerivAt u (deriv u t) t :=
    huDiff.differentiableAt.hasDerivAt
  have hlinear : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using
      (hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_id t)
  have hexp2 :
      HasDerivAt (fun s : ℝ => Real.exp (2 * s))
        (2 * Real.exp (2 * t)) t := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (2 * t)).comp t hlinear
  have hyDeriv :
      HasDerivAt (fun s : ℝ => u s * Real.exp (2 * s))
        (deriv u t * Real.exp (2 * t) +
          u t * (2 * Real.exp (2 * t))) t :=
    huDeriv.mul hexp2
  rw [hyDeriv.deriv, (Real.hasDerivAt_exp t).deriv]
  ring

theorem gap3 (u : ℝ → ℝ) :
    ∀ t,
      Real.exp (2 * t) * (2 * u t + d1 u t) /
          Real.exp t =
        Real.exp t * (2 * u t + d1 u t) := by
  intro t
  rw [show 2 * t = t + t by ring, Real.exp_add]
  apply (div_eq_iff (Real.exp_ne_zero t)).2
  ring

theorem gap4 (x y u : ℝ → ℝ)
    (hDefinition :
      ∀ t, dydx x y t = d1 y t / d1 x t)
    (hExpand :
      ∀ t,
        d1 y t / d1 x t =
          Real.exp (2 * t) * (2 * u t + d1 u t) /
            Real.exp t)
    (hCancel :
      ∀ t,
        Real.exp (2 * t) * (2 * u t + d1 u t) /
            Real.exp t =
          Real.exp t * (2 * u t + d1 u t)) :
    ∀ t,
      dydx x y t =
        Real.exp t * (2 * u t + d1 u t) := by
  intro t
  calc
    dydx x y t = d1 y t / d1 x t := hDefinition t
    _ = Real.exp (2 * t) * (2 * u t + d1 u t) / Real.exp t :=
      hExpand t
    _ = Real.exp t * (2 * u t + d1 u t) := hCancel t

theorem gap5 (x y : ℝ → ℝ) (t : ℝ)
    (hRegular : d1 x t ≠ 0) :
    d2ydx2 x y t = d1 (dydx x y) t / d1 x t := by
  rfl

theorem gap6 (x y u : ℝ → ℝ)
    (hXDerivative : ∀ t, d1 x t = Real.exp t)
    (hFirst :
      ∀ t,
        dydx x y t =
          Real.exp t * (2 * u t + d1 u t))
    (hu : ContDiff ℝ 2 u) :
    ∀ t,
      d1 (dydx x y) t / d1 x t =
        Real.exp t * (d2 u t + 3 * d1 u t + 2 * u t) /
          Real.exp t := by
  intro t
  rw [hXDerivative t]
  have hfun :
      dydx x y = fun s : ℝ =>
        Real.exp s * (2 * u s + d1 u s) :=
    funext hFirst
  rw [hfun]
  unfold d1 d2
  have huDiff : Differentiable ℝ u :=
    hu.differentiable (by decide)
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ u) := by
    exact
      ((contDiff_succ_iff_fderiv (n := 1)).mp
        (show ContDiff ℝ (1 + 1) u by simpa using hu)).2.2
  have hfderivDiff : Differentiable ℝ (fderiv ℝ u) :=
    hfderivCont.differentiable (by decide)
  have hduDiff : Differentiable ℝ (deriv u) := by
    change Differentiable ℝ (fun s : ℝ => (fderiv ℝ u s) (1 : ℝ))
    exact
      hfderivDiff.clm_apply
        (differentiable_const (c := (1 : ℝ)))
  have huDeriv : HasDerivAt u (deriv u t) t :=
    huDiff.differentiableAt.hasDerivAt
  have hduDeriv :
      HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hduDiff.differentiableAt.hasDerivAt
  have htwoU :
      HasDerivAt (fun s : ℝ => 2 * u s) (2 * deriv u t) t := by
    simpa using
      (hasDerivAt_const t (2 : ℝ)).mul huDeriv
  have hinner :
      HasDerivAt (fun s : ℝ => 2 * u s + deriv u s)
        (2 * deriv u t + deriv (deriv u) t) t :=
    htwoU.add hduDeriv
  have hproduct :
      HasDerivAt
        (fun s : ℝ => Real.exp s * (2 * u s + deriv u s))
        (Real.exp t * (2 * u t + deriv u t) +
          Real.exp t * (2 * deriv u t + deriv (deriv u) t)) t :=
    (Real.hasDerivAt_exp t).mul hinner
  rw [hproduct.deriv]
  ring

theorem gap7 (u : ℝ → ℝ) :
    ∀ t,
      Real.exp t * (d2 u t + 3 * d1 u t + 2 * u t) /
          Real.exp t =
        d2 u t + 3 * d1 u t + 2 * u t := by
  intro t
  apply (div_eq_iff (Real.exp_ne_zero t)).2
  ring

theorem gap8 (x y u : ℝ → ℝ)
    (hDefinition :
      ∀ t,
        d2ydx2 x y t = d1 (dydx x y) t / d1 x t)
    (hExpand :
      ∀ t,
        d1 (dydx x y) t / d1 x t =
          Real.exp t * (d2 u t + 3 * d1 u t + 2 * u t) /
            Real.exp t)
    (hCancel :
      ∀ t,
        Real.exp t * (d2 u t + 3 * d1 u t + 2 * u t) /
            Real.exp t =
          d2 u t + 3 * d1 u t + 2 * u t) :
    ∀ t,
      d2ydx2 x y t =
        d2 u t + 3 * d1 u t + 2 * u t := by
  intro t
  calc
    d2ydx2 x y t = d1 (dydx x y) t / d1 x t := hDefinition t
    _ = Real.exp t * (d2 u t + 3 * d1 u t + 2 * u t) / Real.exp t :=
      hExpand t
    _ = d2 u t + 3 * d1 u t + 2 * u t := hCancel t

theorem gap9 (x y u : ℝ → ℝ)
    (hODE :
      ∀ t,
        (x t) ^ 4 * d2ydx2 x y t +
            x t * y t * dydx x y t -
            2 * (y t) ^ 2 =
          0)
    (hX : ∀ t, x t = Real.exp t)
    (hY : ∀ t, y t = u t * Real.exp (2 * t))
    (hFirst :
      ∀ t,
        dydx x y t =
          Real.exp t * (2 * u t + d1 u t))
    (hSecond :
      ∀ t,
        d2ydx2 x y t =
          d2 u t + 3 * d1 u t + 2 * u t) :
    ∀ t,
      d2 u t + (u t + 3) * d1 u t + 2 * u t = 0 := by
  intro t
  have ht := hODE t
  rw [hX t, hY t, hFirst t, hSecond t] at ht
  rw [show 2 * t = t + t by ring, Real.exp_add] at ht
  have hfactor :
      (Real.exp t) ^ 4 *
          (d2 u t + (u t + 3) * d1 u t + 2 * u t) = 0 := by
    ring_nf at ht ⊢
    exact ht
  exact
    (mul_eq_zero.mp hfactor).resolve_left
      (pow_ne_zero 4 (Real.exp_ne_zero t))

end

end ProofGap.Exercise3439
