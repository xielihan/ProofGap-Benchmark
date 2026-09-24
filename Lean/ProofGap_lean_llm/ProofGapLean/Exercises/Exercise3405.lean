import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3405

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => partialX f t y) x
def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => partialX f x t) y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) := deriv (fun t => partialY f x t) y
def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) :=
  partialX f x y * dx + partialY f x y * dy
def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) :=
  partialXX f x y * dx ^ 2 + 2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2
def secSq (q : ℝ) := 1 / (Real.cos q) ^ 2

def vFirstEquation (v : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : Prop :=
  secSq (v x y / y) * ((y * differential v x y dx dy - v x y * dy) / y ^ 2) =
    (x * dy - y * dx) / x ^ 2

def vSecondEquation (v : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : Prop :=
  2 * secSq (v x y / y) * Real.tan (v x y / y) *
      ((y * differential v x y dx dy - v x y * dy) / y ^ 2) ^ 2 +
    secSq (v x y / y) *
      ((y ^ 2 * secondDifferential v x y dx dy -
          2 * (y * differential v x y dx dy - v x y * dy) * dy) / y ^ 3) =
    (-2 * (x * dy - y * dx) * dx) / x ^ 3

def uFirstEquation (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : Prop :=
  2 * Real.exp (2 * u x y / x) *
      ((x * differential u x y dx dy - u x y * dx) / x ^ 2) =
    x * dx + y * dy

def uSecondEquation (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : Prop :=
  4 * Real.exp (2 * u x y / x) *
      ((x * differential u x y dx dy - u x y * dx) / x ^ 2) ^ 2 +
    2 * Real.exp (2 * u x y / x) *
      ((x ^ 2 * secondDifferential u x y dx dy -
          2 * (x * differential u x y dx dy - u x y * dx) * dx) / x ^ 3) =
    dx ^ 2 + dy ^ 2

private theorem partialX_eq_fderiv (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    partialX f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (1, 0) := by
  unfold partialX
  have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h := (hf.hasFDerivAt.comp x hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem partialY_eq_fderiv (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    partialY f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (0, 1) := by
  unfold partialY
  have hp : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h := (hf.hasFDerivAt.comp y hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem hasDerivAt_along_line (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f (x + t * dx) (y + t * dy))
      (differential f x y dx dy) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (x + t * dx, y + t * dy))
      (dx, dy) 0 := by
    have hpx := (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx)
    have hpy := (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy)
    convert (hpx.hasFDerivAt.prodMk hpy.hasFDerivAt).hasDerivAt using 1 <;>
      simp [id]
  have hout : HasFDerivAt (Function.uncurry f)
      (fderiv ℝ (Function.uncurry f) (x, y)) (x, y) := hf.hasFDerivAt
  have hout0 : HasFDerivAt (Function.uncurry f)
      (fderiv ℝ (Function.uncurry f) (x, y))
      ((fun t : ℝ => (x + t * dx, y + t * dy)) 0) := by
    simpa using hout
  have hcomp := hout0.comp 0 hp.hasFDerivAt
  have h : HasDerivAt (fun t => f (x + t * dx) (y + t * dy))
      (fderiv ℝ (Function.uncurry f) (x, y) (dx, dy)) 0 := by
    convert hcomp.hasDerivAt using 1 <;> simp [Function.uncurry]
  unfold differential
  rw [partialX_eq_fderiv f x y hf, partialY_eq_fderiv f x y hf]
  convert h using 1
  calc
    fderiv ℝ (Function.uncurry f) (x, y) (1, 0) * dx +
          fderiv ℝ (Function.uncurry f) (x, y) (0, 1) * dy =
        dx • fderiv ℝ (Function.uncurry f) (x, y) (1, 0) +
          dy • fderiv ℝ (Function.uncurry f) (x, y) (0, 1) := by
            simp [smul_eq_mul]
            ring
    _ = fderiv ℝ (Function.uncurry f) (x, y)
          (dx • (1, 0) + dy • (0, 1)) := by
            rw [map_add, map_smul, map_smul]
    _ = fderiv ℝ (Function.uncurry f) (x, y) (dx, dy) := by
      congr 1
      ext <;> simp

private theorem secondDifferential_eq_sndFDeriv
    (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    secondDifferential f x y dx dy =
      fderiv ℝ (fderiv ℝ (Function.uncurry f)) (x, y)
        (dx, dy) (dx, dy) := by
  let F := Function.uncurry f
  let H := fderiv ℝ (fderiv ℝ F) (x, y)
  have hDfDiff : DifferentiableAt ℝ (fderiv ℝ F) (x, y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hfEv := hf.eventually (by simp)
  have hpx :
      (fun p : ℝ × ℝ => partialX f p.1 p.2) =ᶠ[nhds (x, y)]
        (fun p => fderiv ℝ F p (1, 0)) := by
    filter_upwards [hfEv] with p hp
    convert partialX_eq_fderiv f p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [F]
  have hpy :
      (fun p : ℝ × ℝ => partialY f p.1 p.2) =ᶠ[nhds (x, y)]
        (fun p => fderiv ℝ F p (0, 1)) := by
    filter_upwards [hfEv] with p hp
    convert partialY_eq_fderiv f p.1 p.2
      (hp.differentiableAt (by decide)) using 1 <;> simp [F]
  have hxcont : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) := by
    have h : ContinuousAt (fun t : ℝ => (t, y)) x := by fun_prop
    exact h
  have hycont : Filter.Tendsto (fun t : ℝ => (x, t))
      (nhds y) (nhds (x, y)) := by
    have h : ContinuousAt (fun t : ℝ => (x, t)) y := by fun_prop
    exact h
  have hcx : HasFDerivAt (fun t : ℝ => (t, y))
      (ContinuousLinearMap.inl ℝ ℝ ℝ) x :=
    hasFDerivAt_prodMk_left x y
  have hcy : HasFDerivAt (fun t : ℝ => (x, t))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) y :=
    hasFDerivAt_prodMk_right x y
  have hEvalX : HasFDerivAt (fun p : ℝ × ℝ => fderiv ℝ F p (1, 0))
      (H.flip (1, 0)) (x, y) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × ℝ) (x, y))
    convert h using 1 <;> simp [H]
  have hEvalY : HasFDerivAt (fun p : ℝ × ℝ => fderiv ℝ F p (0, 1))
      (H.flip (0, 1)) (x, y) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const ((0, 1) : ℝ × ℝ) (x, y))
    convert h using 1 <;> simp [H]
  have hxxD : HasDerivAt
      (fun t => fderiv ℝ F (t, y) (1, 0)) (H (1, 0) (1, 0)) x := by
    convert (hEvalX.comp x hcx).hasDerivAt using 1 <;> simp
  have hxyD : HasDerivAt
      (fun t => fderiv ℝ F (x, t) (1, 0)) (H (0, 1) (1, 0)) y := by
    convert (hEvalX.comp y hcy).hasDerivAt using 1 <;> simp
  have hyyD : HasDerivAt
      (fun t => fderiv ℝ F (x, t) (0, 1)) (H (0, 1) (0, 1)) y := by
    convert (hEvalY.comp y hcy).hasDerivAt using 1 <;> simp
  have hxx := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hpx hxcont)
  have hxy := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hpx hycont)
  have hyy := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hpy hycont)
  have hXX : partialXX f x y = H (1, 0) (1, 0) := by
    change deriv (fun t => partialX f t y) x = _
    have hxx' :
        deriv (fun t => partialX f t y) x =
          deriv (fun t => fderiv ℝ F (t, y) (1, 0)) x := by
      simpa [Function.comp_def] using hxx
    rw [hxx', hxxD.deriv]
  have hXY : partialXY f x y = H (0, 1) (1, 0) := by
    change deriv (fun t => partialX f x t) y = _
    have hxy' :
        deriv (fun t => partialX f x t) y =
          deriv (fun t => fderiv ℝ F (x, t) (1, 0)) y := by
      simpa [Function.comp_def] using hxy
    rw [hxy', hxyD.deriv]
  have hYY : partialYY f x y = H (0, 1) (0, 1) := by
    change deriv (fun t => partialY f x t) y = _
    have hyy' :
        deriv (fun t => partialY f x t) y =
          deriv (fun t => fderiv ℝ F (x, t) (0, 1)) y := by
      simpa [Function.comp_def] using hyy
    rw [hyy', hyyD.deriv]
  have hsymm : H (1, 0) (0, 1) = H (0, 1) (1, 0) := by
    exact (hf.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1)
  unfold secondDifferential
  rw [hXX, hXY, hYY]
  change _ = H (dx, dy) (dx, dy)
  rw [show (dx, dy) = dx • (1, 0) + dy • (0, 1) by ext <;> simp]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  rw [hsymm]
  simp [smul_eq_mul]
  ring

private theorem hasDerivAt_differential_along_line
    (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    HasDerivAt
      (fun t => differential f (x + t * dx) (y + t * dy) dx dy)
      (secondDifferential f x y dx dy) 0 := by
  let F := Function.uncurry f
  let H := fderiv ℝ (fderiv ℝ F) (x, y)
  let d : ℝ × ℝ := (dx, dy)
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hfEv := hf.eventually (by simp)
  have hDiff :
      (fun p : ℝ × ℝ => differential f p.1 p.2 dx dy) =ᶠ[nhds (x, y)]
        (fun p => fderiv ℝ F p d) := by
    filter_upwards [hfEv] with p hp
    unfold differential
    rw [partialX_eq_fderiv f p.1 p.2
      (hp.differentiableAt (by decide))]
    rw [partialY_eq_fderiv f p.1 p.2
      (hp.differentiableAt (by decide))]
    change fderiv ℝ F p (1, 0) * dx +
        fderiv ℝ F p (0, 1) * dy = fderiv ℝ F p (dx, dy)
    calc
      fderiv ℝ F p (1, 0) * dx + fderiv ℝ F p (0, 1) * dy =
          dx • fderiv ℝ F p (1, 0) + dy • fderiv ℝ F p (0, 1) := by
        simp [smul_eq_mul]
        ring
      _ = fderiv ℝ F p (dx • (1, 0) + dy • (0, 1)) := by
        rw [map_add, map_smul, map_smul]
      _ = fderiv ℝ F p (dx, dy) := by
        congr 1
        ext <;> simp
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have hLineEq := Filter.EventuallyEq.comp_tendsto hDiff hc
  have hp : HasDerivAt c d 0 := by
    have hpx := (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx)
    have hpy := (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy)
    convert (hpx.hasFDerivAt.prodMk hpy.hasFDerivAt).hasDerivAt using 1 <;>
      simp [c, d, id]
  have hDfDiff : DifferentiableAt ℝ (fderiv ℝ F) (x, y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hEval : HasFDerivAt (fun p : ℝ × ℝ => fderiv ℝ F p d)
      (H.flip d) (x, y) := by
    have h := hDfDiff.hasFDerivAt.clm_apply
      (hasFDerivAt_const d (x, y))
    convert h using 1 <;> simp [H]
  have hEval0 : HasFDerivAt (fun p : ℝ × ℝ => fderiv ℝ F p d)
      (H.flip d) (c 0) := by
    simpa [c] using hEval
  have hright : HasDerivAt (fun t => fderiv ℝ F (c t) d)
      (H d d) 0 := by
    convert (hEval0.comp 0 hp.hasFDerivAt).hasDerivAt using 1 <;>
      simp [H, d, c]
  have hd := Filter.EventuallyEq.deriv_eq hLineEq
  have hd' :
      deriv (fun t => differential f (x + t * dx) (y + t * dy) dx dy) 0 =
        deriv (fun t => fderiv ℝ F (c t) d) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hright.deriv] at hd'
  have hLineEq' :
      (fun t => differential f (x + t * dx) (y + t * dy) dx dy) =ᶠ[nhds 0]
        (fun t => fderiv ℝ F (c t) d) := by
    simpa [c, Function.comp_def] using hLineEq
  rw [secondDifferential_eq_sndFDeriv f x y dx dy hf]
  change HasDerivAt _ (H d d) 0
  exact HasDerivAt.congr_of_eventuallyEq hright hLineEq'

private theorem hasDerivAt_quotient_first
    (f f' : ℝ → ℝ) (g : ℝ → ℝ) (t f₀ f₁ f₂ g₀ g₁ : ℝ)
    (hf : HasDerivAt f f₁ t)
    (hf' : HasDerivAt f' f₂ t)
    (hg : HasDerivAt g g₁ t)
    (hf0 : f t = f₀) (hfp0 : f' t = f₁) (hg0 : g t = g₀)
    (hgn : g₀ ≠ 0) :
    HasDerivAt
      (fun s => (g s * f' s - f s * g₁) / (g s) ^ 2)
      ((g₀ ^ 2 * f₂ - 2 * (g₀ * f₁ - f₀ * g₁) * g₁) /
        g₀ ^ 3) t := by
  have hnum :=
    (hg.mul hf').sub (hf.mul_const g₁)
  have hden := hg.pow 2
  convert hnum.div hden (by simpa [hg0] using pow_ne_zero 2 hgn) using 1 <;>
    simp [hf0, hfp0, hg0] <;> field_simp [hgn] <;> ring

private theorem hasDerivAt_along_line_at
    (f : ℝ → ℝ → ℝ) (x y dx dy t : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f)
      (x + t * dx, y + t * dy)) :
    HasDerivAt (fun s => f (x + s * dx) (y + s * dy))
      (differential f (x + t * dx) (y + t * dy) dx dy) t := by
  have h0 := hasDerivAt_along_line f
    (x + t * dx) (y + t * dy) dx dy hf
  have h0' : HasDerivAt
      (fun r => f (x + t * dx + r * dx) (y + t * dy + r * dy))
      (differential f (x + t * dx) (y + t * dy) dx dy) (t - t) := by
    simpa using h0
  have hs : HasDerivAt (fun s : ℝ => s - t) 1 t :=
    (hasDerivAt_id t).sub_const t
  have hc : HasDerivAt
      (fun s => f (x + t * dx + (s - t) * dx)
        (y + t * dy + (s - t) * dy))
      (differential f (x + t * dx) (y + t * dy) dx dy) t :=
    by
      simpa only [Function.comp_apply, mul_one] using
        HasDerivAt.comp (x := t) (h := fun s : ℝ => s - t) h0' hs
  convert hc using 1
  funext s
  congr 1 <;> ring

private theorem hasDerivAt_differential_along_line_at
    (f : ℝ → ℝ → ℝ) (x y dx dy t : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f)
      (x + t * dx, y + t * dy)) :
    HasDerivAt
      (fun s => differential f (x + s * dx) (y + s * dy) dx dy)
      (secondDifferential f (x + t * dx) (y + t * dy) dx dy) t := by
  have h0 := hasDerivAt_differential_along_line f
    (x + t * dx) (y + t * dy) dx dy hf
  have h0' : HasDerivAt
      (fun r => differential f
        (x + t * dx + r * dx) (y + t * dy + r * dy) dx dy)
      (secondDifferential f (x + t * dx) (y + t * dy) dx dy) (t - t) := by
    simpa using h0
  have hs : HasDerivAt (fun s : ℝ => s - t) 1 t :=
    (hasDerivAt_id t).sub_const t
  have hc : HasDerivAt
      (fun s => differential f
        (x + t * dx + (s - t) * dx) (y + t * dy + (s - t) * dy) dx dy)
      (secondDifferential f (x + t * dx) (y + t * dy) dx dy) t :=
    by
      simpa only [Function.comp_apply, mul_one] using
        HasDerivAt.comp (x := t) (h := fun s : ℝ => s - t) h0' hs
  convert hc using 1
  funext s
  congr 1 <;> ring

theorem gap1 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hCos : Real.cos (v x y / y) ≠ 0)
    (h1 : Real.exp (u x y / x) * Real.cos (v x y / y) = x / Real.sqrt 2)
    (h2 : Real.exp (u x y / x) * Real.sin (v x y / y) = y / Real.sqrt 2) :
    Real.tan (v x y / y) = y / x := by
  have hs : Real.sqrt 2 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have hxEq :
      x = Real.exp (u x y / x) * Real.cos (v x y / y) * Real.sqrt 2 :=
    ((eq_div_iff hs).mp h1).symm
  have hyEq :
      y = Real.exp (u x y / x) * Real.sin (v x y / y) * Real.sqrt 2 :=
    ((eq_div_iff hs).mp h2).symm
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hx, hCos]
  linear_combination
    Real.sin (v x y / y) * hxEq -
      Real.cos (v x y / y) * hyEq

theorem gap2 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : Real.exp (u x y / x) * Real.cos (v x y / y) = x / Real.sqrt 2)
    (h2 : Real.exp (u x y / x) * Real.sin (v x y / y) = y / Real.sqrt 2) :
    Real.exp (2 * u x y / x) = (x ^ 2 + y ^ 2) / 2 := by
  have hs : Real.sqrt 2 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have hxEq :
      x = Real.exp (u x y / x) * Real.cos (v x y / y) * Real.sqrt 2 :=
    ((eq_div_iff hs).mp h1).symm
  have hyEq :
      y = Real.exp (u x y / x) * Real.sin (v x y / y) * Real.sqrt 2 :=
    ((eq_div_iff hs).mp h2).symm
  calc
    Real.exp (2 * u x y / x) =
        Real.exp (u x y / x) ^ 2 := by
      rw [show 2 * u x y / x = u x y / x + u x y / x by ring,
        Real.exp_add]
      ring
    _ = ((Real.exp (u x y / x) * Real.cos (v x y / y) * Real.sqrt 2) ^ 2 +
          (Real.exp (u x y / x) * Real.sin (v x y / y) * Real.sqrt 2) ^ 2) /
        2 := by
      calc
        Real.exp (u x y / x) ^ 2 =
            Real.exp (u x y / x) ^ 2 *
              (Real.cos (v x y / y) ^ 2 + Real.sin (v x y / y) ^ 2) := by
          rw [Real.cos_sq_add_sin_sq]
          ring
        _ = _ := by
          rw [show
            (Real.exp (u x y / x) * Real.cos (v x y / y) * Real.sqrt 2) ^ 2 =
              Real.exp (u x y / x) ^ 2 * Real.cos (v x y / y) ^ 2 *
                (Real.sqrt 2) ^ 2 by ring]
          rw [show
            (Real.exp (u x y / x) * Real.sin (v x y / y) * Real.sqrt 2) ^ 2 =
              Real.exp (u x y / x) ^ 2 * Real.sin (v x y / y) ^ 2 *
                (Real.sqrt 2) ^ 2 by ring]
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
    _ = (x ^ 2 + y ^ 2) / 2 := by
      rw [← hxEq, ← hyEq]

theorem gap3 (v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hTan : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Real.tan (v p.1 p.2 / p.2) = p.2 / p.1) :
    vFirstEquation v x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hTan hc
  have hTanAt := mem_of_mem_nhds hTan
  change Real.tan (v x y / y) = y / x at hTanAt
  have hCos : Real.cos (v x y / y) ≠ 0 := by
    intro h
    rw [Real.tan_eq_sin_div_cos, h, div_zero] at hTanAt
    exact (div_ne_zero hy hx) hTanAt.symm
  have hvLine := hasDerivAt_along_line v x y dx dy hvDiff
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hleft :
      HasDerivAt
        (fun t => Real.tan
          (v (x + t * dx) (y + t * dy) / (y + t * dy)))
        (secSq (v x y / y) *
          ((y * differential v x y dx dy - v x y * dy) / y ^ 2)) 0 := by
    have hCos0 : Real.cos
        (v (x + 0 * dx) (y + 0 * dy) / (y + 0 * dy)) ≠ 0 := by
      simpa using hCos
    have ht := (Real.hasDerivAt_tan hCos0).comp 0
      (hvLine.div hyLine (by simpa using hy))
    convert ht using 1
    simp only [secSq, zero_mul, add_zero, div_eq_mul_inv]
    ring
  have hright :
      HasDerivAt (fun t => (y + t * dy) / (x + t * dx))
        ((x * dy - y * dx) / x ^ 2) 0 := by
    convert hyLine.div hxLine (by simpa using hx) using 1 <;>
      simp <;> field_simp [hx] <;> ring
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv
          (fun t => Real.tan
            (v (x + t * dx) (y + t * dy) / (y + t * dy))) 0 =
        deriv (fun t => (y + t * dy) / (x + t * dx)) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hleft.deriv, hright.deriv] at hd'
  exact hd'

theorem gap4 (v : ℝ → ℝ → ℝ) (dx dy : ℝ)
    (hv : v 1 1 = Real.pi / 4)
    (hFirst : vFirstEquation v 1 1 dx dy) :
    differential v 1 1 dx dy =
      Real.pi / 4 * dy - (1 / 2 : ℝ) * (dx - dy) := by
  unfold vFirstEquation secSq at hFirst
  rw [hv] at hFirst
  norm_num at hFirst
  have hs : Real.sqrt 2 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  field_simp [hs] at hFirst
  have hs2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hs2] at hFirst
  nlinarith

theorem gap5 (v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hvC2 : ContDiffAt ℝ 2 (Function.uncurry v) (x, y))
    (hTan : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Real.tan (v p.1 p.2 / p.2) = p.2 / p.1) :
    vSecondEquation v x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hTan hc
  have hTanAt := mem_of_mem_nhds hTan
  change Real.tan (v x y / y) = y / x at hTanAt
  have hcos : Real.cos (v x y / y) ≠ 0 := by
    intro h
    rw [Real.tan_eq_sin_div_cos, h, div_zero] at hTanAt
    exact (div_ne_zero hy hx) hTanAt.symm
  have hvEv := hc.eventually (hvC2.eventually (by simp))
  have hvLine := hasDerivAt_along_line v x y dx dy
    (hvC2.differentiableAt (by decide))
  have hvD := hasDerivAt_differential_along_line v x y dx dy hvC2
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hq : HasDerivAt
      (fun t => v (x + t * dx) (y + t * dy) / (y + t * dy))
      ((differential v x y dx dy * y - v x y * dy) / y ^ 2) 0 := by
    convert hvLine.div hyLine (by simpa using hy) using 1 <;>
      simp <;> field_simp [hy] <;> ring
  have hyNe := hyLine.continuousAt.eventually_ne (by simpa using hy)
  have hxNe := hxLine.continuousAt.eventually_ne (by simpa using hx)
  have hcosNe := hq.cos.continuousAt.eventually_ne (by simpa using hcos)
  have hld :
      deriv
          (fun t => Real.tan
            (v (x + t * dx) (y + t * dy) / (y + t * dy))) =ᶠ[nhds 0]
        (fun t => secSq
          (v (x + t * dx) (y + t * dy) / (y + t * dy)) *
            ((y + t * dy) *
                differential v (x + t * dx) (y + t * dy) dx dy -
              v (x + t * dx) (y + t * dy) * dy) /
              (y + t * dy) ^ 2) := by
    filter_upwards [hvEv, hyNe, hcosNe] with t ht hyt hct
    have hvT := hasDerivAt_along_line_at v x y dx dy t
      (ht.differentiableAt (by decide))
    have hyT : HasDerivAt (fun s => y + s * dy) dy t := by
      convert (hasDerivAt_const t y).add
        ((hasDerivAt_id t).mul_const dy) using 1 <;> simp [id]
    have hqt : HasDerivAt
        (fun s => v (x + s * dx) (y + s * dy) / (y + s * dy))
        ((differential v (x + t * dx) (y + t * dy) dx dy *
            (y + t * dy) - v (x + t * dx) (y + t * dy) * dy) /
          (y + t * dy) ^ 2) t := by
      convert hvT.div hyT hyt using 1 <;>
        simp <;> field_simp [hyt] <;> ring
    have htt : HasDerivAt
        (fun s => Real.tan
          (v (x + s * dx) (y + s * dy) / (y + s * dy)))
        (1 / Real.cos
            (v (x + t * dx) (y + t * dy) / (y + t * dy)) ^ 2 *
          ((differential v (x + t * dx) (y + t * dy) dx dy *
              (y + t * dy) -
            v (x + t * dx) (y + t * dy) * dy) /
            (y + t * dy) ^ 2)) t := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_tan hct).comp t hqt
    rw [htt.deriv]
    simp only [secSq, div_eq_mul_inv]
    ring
  have hrd :
      deriv (fun t => (y + t * dy) / (x + t * dx)) =ᶠ[nhds 0]
        (fun t => ((x + t * dx) * dy - (y + t * dy) * dx) /
          (x + t * dx) ^ 2) := by
    filter_upwards [hxNe] with t hxt
    have hxT : HasDerivAt (fun s => x + s * dx) dx t := by
      convert (hasDerivAt_const t x).add
        ((hasDerivAt_id t).mul_const dx) using 1 <;> simp [id]
    have hyT : HasDerivAt (fun s => y + s * dy) dy t := by
      convert (hasDerivAt_const t y).add
        ((hasDerivAt_id t).mul_const dy) using 1 <;> simp [id]
    have hdiv : HasDerivAt
        (fun s => (y + s * dy) / (x + s * dx))
        ((dy * (x + t * dx) - (y + t * dy) * dx) /
          (x + t * dx) ^ 2) t := by
      simpa only [Pi.div_apply] using hyT.div hxT hxt
    rw [hdiv.deriv]
    simp only [div_eq_mul_inv]
    ring
  have hfirst := hld.symm.trans ((Filter.EventuallyEq.deriv he).trans hrd)
  have hqFirst :=
    hasDerivAt_quotient_first
      (fun t => v (x + t * dx) (y + t * dy))
      (fun t => differential v (x + t * dx) (y + t * dy) dx dy)
      (fun t => y + t * dy) 0 (v x y)
      (differential v x y dx dy) (secondDifferential v x y dx dy)
      y dy hvLine hvD hyLine (by simp) (by simp) (by simp) hy
  have hsec :
      HasDerivAt
        (fun t => secSq
          (v (x + t * dx) (y + t * dy) / (y + t * dy)))
        (2 * secSq (v x y / y) * Real.tan (v x y / y) *
          ((y * differential v x y dx dy - v x y * dy) / y ^ 2)) 0 := by
    unfold secSq
    convert (hq.cos.pow 2).inv (by simpa using pow_ne_zero 2 hcos) using 1
    · funext t
      simp [secSq, div_eq_mul_inv]
    · simp [Real.tan_eq_sin_div_cos]
      field_simp [hy, hcos]
  have hleft : HasDerivAt
      (fun t => secSq
          (v (x + t * dx) (y + t * dy) / (y + t * dy)) *
        (((y + t * dy) *
              differential v (x + t * dx) (y + t * dy) dx dy -
            v (x + t * dx) (y + t * dy) * dy) /
          (y + t * dy) ^ 2))
      (2 * secSq (v x y / y) * Real.tan (v x y / y) *
          ((y * differential v x y dx dy - v x y * dy) / y ^ 2) ^ 2 +
        secSq (v x y / y) *
          ((y ^ 2 * secondDifferential v x y dx dy -
              2 * (y * differential v x y dx dy - v x y * dy) * dy) /
            y ^ 3)) 0 := by
    convert hsec.mul hqFirst using 1 <;> simp <;> ring
  have hright :=
    hasDerivAt_quotient_first
      (fun t => y + t * dy) (fun _ => dy) (fun t => x + t * dx)
      0 y dy 0 x dx hyLine (hasDerivAt_const 0 dy) hxLine
      (by simp) (by simp) (by simp) hx
  have hfirst' :
      (fun t => secSq
          (v (x + t * dx) (y + t * dy) / (y + t * dy)) *
        (((y + t * dy) *
              differential v (x + t * dx) (y + t * dy) dx dy -
            v (x + t * dx) (y + t * dy) * dy) /
          (y + t * dy) ^ 2)) =ᶠ[nhds 0]
        (fun t => ((x + t * dx) * dy - (y + t * dy) * dx) /
          (x + t * dx) ^ 2) := by
    filter_upwards [hfirst] with t ht
    rw [← ht]
    ring
  have hd := Filter.EventuallyEq.deriv_eq hfirst'
  rw [hleft.deriv, hright.deriv] at hd
  unfold vSecondEquation
  convert hd using 1 <;> ring

theorem gap6 (v : ℝ → ℝ → ℝ) (dx dy : ℝ)
    (hv : v 1 1 = Real.pi / 4)
    (hFirst : differential v 1 1 dx dy =
      Real.pi / 4 * dy - (1 / 2 : ℝ) * (dx - dy))
    (hSecond : vSecondEquation v 1 1 dx dy) :
    secondDifferential v 1 1 dx dy = (1 / 2 : ℝ) * (dx - dy) ^ 2 := by
  unfold vSecondEquation secSq at hSecond
  rw [hv, hFirst] at hSecond
  norm_num at hSecond
  have hs : Real.sqrt 2 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  field_simp [hs] at hSecond
  have hs2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hs2] at hSecond
  nlinarith

theorem gap7 (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hx : x ≠ 0)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hExp : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Real.exp (2 * u p.1 p.2 / p.1) = (p.1 ^ 2 + p.2 ^ 2) / 2) :
    uFirstEquation u x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hExp hc
  have huLine := hasDerivAt_along_line u x y dx dy huDiff
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hleft :
      HasDerivAt
        (fun t => Real.exp
          (2 * u (x + t * dx) (y + t * dy) / (x + t * dx)))
        (2 * Real.exp (2 * u x y / x) *
          ((x * differential u x y dx dy - u x y * dx) / x ^ 2)) 0 := by
    convert ((huLine.const_mul 2).div hxLine (by simpa using hx)).exp using 1 <;>
      simp <;> field_simp [hx] <;> ring
  have hright :
      HasDerivAt
        (fun t => ((x + t * dx) ^ 2 + (y + t * dy) ^ 2) / 2)
        (x * dx + y * dy) 0 := by
    convert ((hxLine.pow 2).add (hyLine.pow 2)).div_const 2 using 1 <;>
      norm_num <;> ring
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv
          (fun t => Real.exp
            (2 * u (x + t * dx) (y + t * dy) / (x + t * dx))) 0 =
        deriv
          (fun t => ((x + t * dx) ^ 2 + (y + t * dy) ^ 2) / 2) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hleft.deriv, hright.deriv] at hd'
  exact hd'

theorem gap8 (u : ℝ → ℝ → ℝ) (dx dy : ℝ)
    (hu : u 1 1 = 0)
    (hFirst : uFirstEquation u 1 1 dx dy) :
    differential u 1 1 dx dy = (dx + dy) / 2 := by
  unfold uFirstEquation at hFirst
  rw [hu] at hFirst
  norm_num at hFirst ⊢
  linarith

theorem gap9 (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hx : x ≠ 0)
    (huC2 : ContDiffAt ℝ 2 (Function.uncurry u) (x, y))
    (hExp : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Real.exp (2 * u p.1 p.2 / p.1) = (p.1 ^ 2 + p.2 ^ 2) / 2) :
    uSecondEquation u x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hExp hc
  have huEv := hc.eventually (huC2.eventually (by simp))
  have huLine := hasDerivAt_along_line u x y dx dy
    (huC2.differentiableAt (by decide))
  have huD := hasDerivAt_differential_along_line u x y dx dy huC2
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hq : HasDerivAt
      (fun t => 2 * u (x + t * dx) (y + t * dy) / (x + t * dx))
      ((2 * differential u x y dx dy * x - 2 * u x y * dx) / x ^ 2) 0 := by
    convert (huLine.const_mul 2).div hxLine (by simpa using hx) using 1 <;>
      simp <;> field_simp [hx] <;> ring
  have hxNe : ∀ᶠ z : ℝ in nhds 0, x + z * dx ≠ 0 :=
    hxLine.continuousAt.eventually_ne (by simpa using hx)
  have hld :
      deriv
          (fun t => Real.exp
            (2 * u (x + t * dx) (y + t * dy) / (x + t * dx))) =ᶠ[nhds 0]
        (fun t => Real.exp
            (2 * u (x + t * dx) (y + t * dy) / (x + t * dx)) *
          (2 * ((x + t * dx) *
                differential u (x + t * dx) (y + t * dy) dx dy -
              u (x + t * dx) (y + t * dy) * dx) /
            (x + t * dx) ^ 2)) := by
    filter_upwards [huEv, hxNe] with t ht hxt
    have huT := hasDerivAt_along_line_at u x y dx dy t
      (ht.differentiableAt (by decide))
    have hxT : HasDerivAt (fun s => x + s * dx) dx t := by
      convert (hasDerivAt_const t x).add
        ((hasDerivAt_id t).mul_const dx) using 1 <;> simp [id]
    have hqt : HasDerivAt
        (fun s => 2 * u (x + s * dx) (y + s * dy) / (x + s * dx))
        ((2 * differential u (x + t * dx) (y + t * dy) dx dy *
              (x + t * dx) -
            2 * u (x + t * dx) (y + t * dy) * dx) /
          (x + t * dx) ^ 2) t := by
      convert (huT.const_mul 2).div hxT hxt using 1 <;>
        simp <;> field_simp [hxt] <;> ring
    have het : HasDerivAt
        (fun s => Real.exp
          (2 * u (x + s * dx) (y + s * dy) / (x + s * dx)))
        (Real.exp
            (2 * u (x + t * dx) (y + t * dy) / (x + t * dx)) *
          ((2 * differential u (x + t * dx) (y + t * dy) dx dy *
                (x + t * dx) -
              2 * u (x + t * dx) (y + t * dy) * dx) /
            (x + t * dx) ^ 2)) t := by
      simpa only [Function.comp_apply] using hqt.exp
    rw [het.deriv]
    simp only [div_eq_mul_inv]
    ring
  have hrd :
      deriv
          (fun t => ((x + t * dx) ^ 2 + (y + t * dy) ^ 2) / 2) =ᶠ[nhds 0]
        (fun t => (x + t * dx) * dx + (y + t * dy) * dy) := by
    filter_upwards with t
    have hxT : HasDerivAt (fun s => x + s * dx) dx t := by
      convert (hasDerivAt_const t x).add
        ((hasDerivAt_id t).mul_const dx) using 1 <;> simp [id]
    have hyT : HasDerivAt (fun s => y + s * dy) dy t := by
      convert (hasDerivAt_const t y).add
        ((hasDerivAt_id t).mul_const dy) using 1 <;> simp [id]
    have hrt : HasDerivAt
        (fun s => ((x + s * dx) ^ 2 + (y + s * dy) ^ 2) / 2)
        ((2 * (x + t * dx) * dx + 2 * (y + t * dy) * dy) / 2) t := by
      convert ((hxT.pow 2).add (hyT.pow 2)).div_const 2 using 1 <;>
        norm_num <;> ring
    rw [hrt.deriv]
    ring
  have hfirst := hld.symm.trans ((Filter.EventuallyEq.deriv he).trans hrd)
  have hqFirst :=
    hasDerivAt_quotient_first
      (fun t => 2 * u (x + t * dx) (y + t * dy))
      (fun t => 2 * differential u (x + t * dx) (y + t * dy) dx dy)
      (fun t => x + t * dx) 0 (2 * u x y)
      (2 * differential u x y dx dy)
      (2 * secondDifferential u x y dx dy)
      x dx (huLine.const_mul 2) (huD.const_mul 2) hxLine
      (by simp) (by simp) (by simp) hx
  have hleft := hq.exp.mul hqFirst
  have hright :=
    (hxLine.mul_const dx).add (hyLine.mul_const dy)
  have hfirst' :
      (fun t =>
        Real.exp (2 * u (x + t * dx) (y + t * dy) / (x + t * dx)) *
          (((x + t * dx) *
                (2 * differential u (x + t * dx) (y + t * dy) dx dy) -
              (2 * u (x + t * dx) (y + t * dy)) * dx) /
            (x + t * dx) ^ 2)) =ᶠ[nhds 0]
        (fun t => (x + t * dx) * dx + (y + t * dy) * dy) := by
    filter_upwards [hfirst] with t ht
    rw [← ht]
    ring
  have hd := Filter.EventuallyEq.deriv_eq hfirst'
  have hd' :
      deriv
          ((fun t => Real.exp
              (2 * u (x + t * dx) (y + t * dy) / (x + t * dx))) *
            (fun t =>
              ((x + t * dx) *
                    (2 * differential u (x + t * dx) (y + t * dy) dx dy) -
                  (2 * u (x + t * dx) (y + t * dy)) * dx) /
                (x + t * dx) ^ 2)) 0 =
        deriv
          ((fun t => (x + t * dx) * dx) +
            (fun t => (y + t * dy) * dy)) 0 := by
    simpa only [Pi.mul_apply, Pi.add_apply] using hd
  rw [hleft.deriv, hright.deriv] at hd'
  unfold uSecondEquation
  convert hd' using 1 <;> field_simp [hx] <;> ring

theorem gap10 (u : ℝ → ℝ → ℝ) (dx dy : ℝ)
    (hu : u 1 1 = 0)
    (hFirst : differential u 1 1 dx dy = (dx + dy) / 2)
    (hSecond : uSecondEquation u 1 1 dx dy) :
    secondDifferential u 1 1 dx dy = dx ^ 2 := by
  unfold uSecondEquation at hSecond
  rw [hu, hFirst] at hSecond
  norm_num at hSecond
  nlinarith

end

end ProofGap.Exercise3405
