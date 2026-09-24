import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3441

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def dydx (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 y t / d1 x t

def d2ydx2 (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 (dydx x y) t / d1 x t

private theorem Real.cosh_ne_zero (t : ℝ) : _root_.Real.cosh t ≠ 0 :=
  ne_of_gt (_root_.Real.cosh_pos t)

private theorem hasDerivAt_tanh_aux (t : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh t ^ 2) t := by
  have hc : Real.cosh t ≠ 0 := ne_of_gt (Real.cosh_pos t)
  have hnum :
      Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t = 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hcoef :
      (Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t) /
          Real.cosh t ^ 2 =
        1 / Real.cosh t ^ 2 := by
    rw [hnum]
  have htanh : Real.tanh = Real.sinh / Real.cosh := by
    funext s
    exact Real.tanh_eq_sinh_div_cosh s
  rw [htanh]
  simpa only [hcoef] using
    ((Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) hc)

private theorem contDiff_deriv_of_order_two (f : ℝ → ℝ)
    (h : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  exact
    (contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) f from h)).2.2

theorem gap1 (x y u : ℝ → ℝ)
    (hX : ∀ t, x t = Real.tanh t)
    (hY : ∀ t, y t = u t / Real.cosh t)
    (hu : ContDiff ℝ 1 u) :
    ∀ t,
      dydx x y t =
        ((d1 u t * Real.cosh t - u t * Real.sinh t) /
            (Real.cosh t) ^ 2) /
          (1 / (Real.cosh t) ^ 2) := by
  intro t
  have hx : x = Real.tanh := funext hX
  have hy : y = fun s => u s / Real.cosh s := funext hY
  have hc : Real.cosh t ≠ 0 := ne_of_gt (Real.cosh_pos t)
  have hu1 : HasDerivAt u (deriv u t) t :=
    (hu.differentiable (by decide)).differentiableAt.hasDerivAt
  have hquot :
      HasDerivAt (fun s => u s / Real.cosh s)
        ((deriv u t * Real.cosh t - u t * Real.sinh t) /
          Real.cosh t ^ 2) t :=
    hu1.div (Real.hasDerivAt_cosh t) hc
  have hyDeriv :
      deriv y t =
        (deriv u t * Real.cosh t - u t * Real.sinh t) /
          Real.cosh t ^ 2 := by
    apply HasDerivAt.deriv
    simpa only [hy] using hquot
  have hxDeriv : deriv x t = 1 / Real.cosh t ^ 2 := by
    apply HasDerivAt.deriv
    simpa only [hx] using (hasDerivAt_tanh_aux t)
  unfold dydx d1
  rw [hyDeriv, hxDeriv]

theorem gap2 (u : ℝ → ℝ) :
    ∀ t,
      ((d1 u t * Real.cosh t - u t * Real.sinh t) /
            (Real.cosh t) ^ 2) /
          (1 / (Real.cosh t) ^ 2) =
        d1 u t * Real.cosh t - u t * Real.sinh t := by
  intro t
  field_simp [Real.cosh_ne_zero t]

theorem gap3 (x y u : ℝ → ℝ)
    (hDefinition :
      ∀ t,
        dydx x y t =
          ((d1 u t * Real.cosh t - u t * Real.sinh t) /
              (Real.cosh t) ^ 2) /
            (1 / (Real.cosh t) ^ 2))
    (hCancel :
      ∀ t,
        ((d1 u t * Real.cosh t - u t * Real.sinh t) /
              (Real.cosh t) ^ 2) /
            (1 / (Real.cosh t) ^ 2) =
          d1 u t * Real.cosh t - u t * Real.sinh t) :
    ∀ t,
      dydx x y t =
        d1 u t * Real.cosh t - u t * Real.sinh t := by
  intro t
  exact (hDefinition t).trans (hCancel t)

theorem gap4 (x y u : ℝ → ℝ)
    (hX : ∀ t, x t = Real.tanh t)
    (hFirst :
      ∀ t,
        dydx x y t =
          d1 u t * Real.cosh t - u t * Real.sinh t)
    (hu : ContDiff ℝ 2 u) :
    ∀ t,
      d2ydx2 x y t =
        (d2 u t * Real.cosh t - u t * Real.cosh t) /
          (1 / (Real.cosh t) ^ 2) := by
  intro t
  have hx : x = Real.tanh := funext hX
  have hfirst :
      dydx x y =
        fun s => d1 u s * Real.cosh s - u s * Real.sinh s :=
    funext hFirst
  have hdu : ContDiff ℝ 1 (deriv u) :=
    contDiff_deriv_of_order_two u hu
  have hu1 : HasDerivAt u (deriv u t) t :=
    (hu.differentiable (by decide)).differentiableAt.hasDerivAt
  have hu2 : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    (hdu.differentiable (by decide)).differentiableAt.hasDerivAt
  have hnum :
      HasDerivAt
        (fun s => deriv u s * Real.cosh s - u s * Real.sinh s)
        ((deriv (deriv u) t * Real.cosh t +
            deriv u t * Real.sinh t) -
          (deriv u t * Real.sinh t + u t * Real.cosh t)) t :=
    (hu2.mul (Real.hasDerivAt_cosh t)).sub
      (hu1.mul (Real.hasDerivAt_sinh t))
  have hdydx :
      HasDerivAt (dydx x y)
        ((deriv (deriv u) t * Real.cosh t +
            deriv u t * Real.sinh t) -
          (deriv u t * Real.sinh t + u t * Real.cosh t)) t := by
    simpa only [hfirst, d1] using hnum
  have hxDeriv : deriv x t = 1 / Real.cosh t ^ 2 := by
    apply HasDerivAt.deriv
    simpa only [hx] using (hasDerivAt_tanh_aux t)
  unfold d2ydx2 d1 d2
  rw [hdydx.deriv, hxDeriv]
  ring

theorem gap5 (u : ℝ → ℝ) :
    ∀ t,
      (d2 u t * Real.cosh t - u t * Real.cosh t) /
          (1 / (Real.cosh t) ^ 2) =
        (d2 u t - u t) * (Real.cosh t) ^ 3 := by
  intro t
  field_simp [Real.cosh_ne_zero t]

theorem gap6 (x y u : ℝ → ℝ)
    (hExpand :
      ∀ t,
        d2ydx2 x y t =
          (d2 u t * Real.cosh t - u t * Real.cosh t) /
            (1 / (Real.cosh t) ^ 2))
    (hCancel :
      ∀ t,
        (d2 u t * Real.cosh t - u t * Real.cosh t) /
            (1 / (Real.cosh t) ^ 2) =
          (d2 u t - u t) * (Real.cosh t) ^ 3) :
    ∀ t,
      d2ydx2 x y t =
        (d2 u t - u t) * (Real.cosh t) ^ 3 := by
  intro t
  exact (hExpand t).trans (hCancel t)

theorem gap7 (x y u : ℝ → ℝ)
    (hODE :
      ∀ t,
        (1 - (x t) ^ 2) ^ 2 * d2ydx2 x y t = -y t)
    (hX : ∀ t, x t = Real.tanh t)
    (hY : ∀ t, y t = u t / Real.cosh t)
    (hSecond :
      ∀ t,
        d2ydx2 x y t =
          (d2 u t - u t) * (Real.cosh t) ^ 3) :
    ∀ t, d2 u t = 0 := by
  intro t
  have hc : Real.cosh t ≠ 0 := ne_of_gt (Real.cosh_pos t)
  have htanh :
      1 - Real.tanh t ^ 2 = 1 / Real.cosh t ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hc] <;> nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have h := hODE t
  rw [hX t, hY t, hSecond t, htanh] at h
  field_simp [hc] at h
  ring_nf at h
  linarith [h]

end

end ProofGap.Exercise3441
