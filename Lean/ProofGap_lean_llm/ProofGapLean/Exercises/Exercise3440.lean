import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3440

noncomputable section

def d1 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t

def d2 (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

def dydx (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 y t / d1 x t

def d2ydx2 (x y : ℝ → ℝ) (t : ℝ) : ℝ :=
  d1 (dydx x y) t / d1 x t

def regular (t : ℝ) : Prop :=
  Real.cos t ≠ 0

theorem gap1 (x y u : ℝ → ℝ)
    (hX : ∀ t, x t = Real.tan t)
    (hY : ∀ t, y t = u t / Real.cos t)
    (hu : ContDiff ℝ 1 u) :
    ∀ t, regular t →
      dydx x y t =
        ((d1 u t * Real.cos t + u t * Real.sin t) /
            (Real.cos t) ^ 2) /
          (1 / (Real.cos t) ^ 2) := by
  intro t ht
  have hc : Real.cos t ≠ 0 := ht
  have hx : x = Real.tan := funext hX
  have hy : y = fun s => u s / Real.cos s := funext hY
  have hu' : HasDerivAt u (d1 u t) t := by
    change HasDerivAt u (deriv u t) t
    exact (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hy' := hu'.div (Real.hasDerivAt_cos t) hc
  have hyder :
      d1 (fun s => u s / Real.cos s) t =
        (d1 u t * Real.cos t + u t * Real.sin t) / (Real.cos t) ^ 2 := by
    change deriv (u / Real.cos) t = _
    convert hy'.deriv using 1 <;> ring
  have hxder : d1 Real.tan t = 1 / (Real.cos t) ^ 2 := by
    change deriv Real.tan t = _
    exact (Real.hasDerivAt_tan hc).deriv
  rw [hx, hy]
  simp only [dydx]
  rw [hyder, hxder]

theorem gap2 (u : ℝ → ℝ) :
    ∀ t, regular t →
      ((d1 u t * Real.cos t + u t * Real.sin t) /
            (Real.cos t) ^ 2) /
          (1 / (Real.cos t) ^ 2) =
        d1 u t * Real.cos t + u t * Real.sin t := by
  intro t ht
  change Real.cos t ≠ 0 at ht
  field_simp [ht] <;> ring

theorem gap3 (x y u : ℝ → ℝ)
    (hDefinition :
      ∀ t, regular t →
        dydx x y t =
          ((d1 u t * Real.cos t + u t * Real.sin t) /
              (Real.cos t) ^ 2) /
            (1 / (Real.cos t) ^ 2))
    (hCancel :
      ∀ t, regular t →
        ((d1 u t * Real.cos t + u t * Real.sin t) /
              (Real.cos t) ^ 2) /
            (1 / (Real.cos t) ^ 2) =
          d1 u t * Real.cos t + u t * Real.sin t) :
    ∀ t, regular t →
      dydx x y t =
        d1 u t * Real.cos t + u t * Real.sin t := by
  intro t ht
  calc
    dydx x y t =
        ((d1 u t * Real.cos t + u t * Real.sin t) /
            (Real.cos t) ^ 2) /
          (1 / (Real.cos t) ^ 2) := hDefinition t ht
    _ = d1 u t * Real.cos t + u t * Real.sin t := hCancel t ht

theorem gap4 (x y u : ℝ → ℝ)
    (hX : ∀ t, x t = Real.tan t)
    (hFirst :
      ∀ t, regular t →
        dydx x y t =
          d1 u t * Real.cos t + u t * Real.sin t)
    (hu : ContDiff ℝ 2 u) :
    ∀ t, regular t →
      d2ydx2 x y t =
        (d2 u t * Real.cos t + u t * Real.cos t) /
          (1 / (Real.cos t) ^ 2) := by
  intro t ht
  have hc : Real.cos t ≠ 0 := ht
  have hu_diff : Differentiable ℝ u := hu.differentiable (by decide)
  have hfamily :
      ContDiff ℝ 2 (Function.uncurry (fun (_ : ℝ) => u)) := by
    change ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.2)
    exact hu.comp contDiff_snd
  have hfu_cont : ContDiff ℝ 1 (fun s : ℝ => fderiv ℝ u s) := by
    have h := hfamily.fderiv
      (contDiff_id : ContDiff ℝ 1 (fun s : ℝ => s)) (by decide)
    simpa [Function.uncurry] using h
  have hfu_diff : Differentiable ℝ (fun s : ℝ => fderiv ℝ u s) :=
    hfu_cont.differentiable (by simp)
  have hu_at : HasDerivAt u (d1 u t) t := by
    change HasDerivAt u (deriv u t) t
    exact hu_diff.differentiableAt.hasDerivAt
  have hdu_at_diff : DifferentiableAt ℝ (deriv u) t := by
    change DifferentiableAt ℝ (fun s => (fderiv ℝ u s) 1) t
    exact hfu_diff.differentiableAt.clm_apply
      (hasDerivAt_const t (1 : ℝ)).differentiableAt
  have hdu_at : HasDerivAt (d1 u) (d2 u t) t := by
    change HasDerivAt (deriv u) (deriv (deriv u) t) t
    exact hdu_at_diff.hasDerivAt
  have hF :
      HasDerivAt
        (fun s => d1 u s * Real.cos s + u s * Real.sin s)
        (d2 u t * Real.cos t + u t * Real.cos t) t := by
    convert
      (hdu_at.mul (Real.hasDerivAt_cos t)).add
        (hu_at.mul (Real.hasDerivAt_sin t)) using 1 <;> ring
  have hlocal :
      (fun s => d1 u s * Real.cos s + u s * Real.sin s) =ᶠ[nhds t]
        dydx x y :=
    (Real.continuous_cos.continuousAt.eventually_ne hc).mono
      (fun s hs => (hFirst s hs).symm)
  have hdy :
      HasDerivAt (dydx x y)
        (d2 u t * Real.cos t + u t * Real.cos t) t :=
    hF.congr_of_eventuallyEq hlocal.symm
  have hx : x = Real.tan := funext hX
  have hxder : deriv x t = 1 / (Real.cos t) ^ 2 := by
    rw [hx]
    exact (Real.hasDerivAt_tan hc).deriv
  simp only [d2ydx2, d1]
  rw [hdy.deriv, hxder]

theorem gap5 (u : ℝ → ℝ) :
    ∀ t, regular t →
      (d2 u t * Real.cos t + u t * Real.cos t) /
          (1 / (Real.cos t) ^ 2) =
        (d2 u t + u t) * (Real.cos t) ^ 3 := by
  intro t ht
  change Real.cos t ≠ 0 at ht
  field_simp [ht] <;> ring

theorem gap6 (x y u : ℝ → ℝ)
    (hExpand :
      ∀ t, regular t →
        d2ydx2 x y t =
          (d2 u t * Real.cos t + u t * Real.cos t) /
            (1 / (Real.cos t) ^ 2))
    (hCancel :
      ∀ t, regular t →
        (d2 u t * Real.cos t + u t * Real.cos t) /
            (1 / (Real.cos t) ^ 2) =
          (d2 u t + u t) * (Real.cos t) ^ 3) :
    ∀ t, regular t →
      d2ydx2 x y t =
        (d2 u t + u t) * (Real.cos t) ^ 3 := by
  intro t ht
  calc
    d2ydx2 x y t =
        (d2 u t * Real.cos t + u t * Real.cos t) /
          (1 / (Real.cos t) ^ 2) := hExpand t ht
    _ = (d2 u t + u t) * (Real.cos t) ^ 3 := hCancel t ht

theorem gap7 (x y u : ℝ → ℝ)
    (hODE :
      ∀ t,
        (1 + (x t) ^ 2) ^ 2 * d2ydx2 x y t = y t)
    (hX : ∀ t, x t = Real.tan t)
    (hY : ∀ t, y t = u t / Real.cos t)
    (hSecond :
      ∀ t, regular t →
        d2ydx2 x y t =
          (d2 u t + u t) * (Real.cos t) ^ 3) :
    ∀ t, regular t →
      d2 u t = 0 := by
  intro t ht
  have hc : Real.cos t ≠ 0 := ht
  have hsec :
      1 + (Real.tan t) ^ 2 = 1 / (Real.cos t) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    calc
      1 + (Real.sin t / Real.cos t) ^ 2 =
          ((Real.sin t) ^ 2 + (Real.cos t) ^ 2) /
            (Real.cos t) ^ 2 := by
              field_simp [hc] <;> ring
      _ = 1 / (Real.cos t) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
  have h := hODE t
  rw [hX t, hY t, hSecond t ht, hsec] at h
  field_simp [hc] at h
  linarith

end

end ProofGap.Exercise3440
