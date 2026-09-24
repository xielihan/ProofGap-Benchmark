import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3399

noncomputable section

def partial1 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => F t b) a

def partial2 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => F a t) b

def partial11 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial1 F t b) a

def partial12 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial1 F a t) b

def partial22 (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial2 F a t) b

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z x t) y

def partialXX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z t y) x

def partialXY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX z x t) y

def partialYY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY z x t) y

def differential (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX z x y * dx + partialY z x y * dy

def secondDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  partialXX z x y * dx ^ 2 +
    2 * partialXY z x y * dx * dy +
    partialYY z x y * dy ^ 2

private def quadratic (f : ℝ → ℝ → ℝ) (a b da db : ℝ) : ℝ :=
  partialXX f a b * da ^ 2 +
    2 * partialXY f a b * da * db +
    partialYY f a b * db ^ 2

def plusArg1 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := x + z x y
def plusArg2 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := y + z x y
def ratioArg1 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := x / z x y
def ratioArg2 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := y / z x y

def evalPlus (G : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  G (plusArg1 z x y) (plusArg2 z x y)

def evalRatio (G : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  G (ratioArg1 z x y) (ratioArg2 z x y)

def plusF1 (F : ℝ → ℝ → ℝ) := evalPlus (partial1 F)
def plusF2 (F : ℝ → ℝ → ℝ) := evalPlus (partial2 F)
def plusF11 (F : ℝ → ℝ → ℝ) := evalPlus (partial11 F)
def plusF12 (F : ℝ → ℝ → ℝ) := evalPlus (partial12 F)
def plusF22 (F : ℝ → ℝ → ℝ) := evalPlus (partial22 F)

def ratioF1 (F : ℝ → ℝ → ℝ) := evalRatio (partial1 F)
def ratioF2 (F : ℝ → ℝ → ℝ) := evalRatio (partial2 F)
def ratioF11 (F : ℝ → ℝ → ℝ) := evalRatio (partial11 F)
def ratioF12 (F : ℝ → ℝ → ℝ) := evalRatio (partial12 F)
def ratioF22 (F : ℝ → ℝ → ℝ) := evalRatio (partial22 F)

def plusSolvedDifferential (F : ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  -(plusF1 F z x y * dx + plusF2 F z x y * dy) /
    (plusF1 F z x y + plusF2 F z x y)

def plusRawSecond (F : ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  -(plusF11 F z x y * (dx + differential z x y dx dy) ^ 2 +
      2 * plusF12 F z x y * (dx + differential z x y dx dy) *
        (dy + differential z x y dx dy) +
      plusF22 F z x y * (dy + differential z x y dx dy) ^ 2) /
    (plusF1 F z x y + plusF2 F z x y)

def plusClosedSecond (F : ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  -((plusF11 F z x y * (plusF2 F z x y) ^ 2 -
      2 * plusF1 F z x y * plusF2 F z x y * plusF12 F z x y +
      plusF22 F z x y * (plusF1 F z x y) ^ 2) /
      (plusF1 F z x y + plusF2 F z x y) ^ 3) *
    (dx - dy) ^ 2

def ratioDenominator (F : ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * ratioF1 F z x y + y * ratioF2 F z x y

def ratioSolvedDifferential (F : ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  z x y * (ratioF1 F z x y * dx + ratioF2 F z x y * dy) /
    ratioDenominator F z x y

def ratioA (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  z x y * dx - x * differential z x y dx dy

def ratioB (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  z x y * dy - y * differential z x y dx dy

def ratioRawSecond (F : ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  (ratioF11 F z x y * (ratioA z x y dx dy) ^ 2 +
      2 * ratioF12 F z x y * ratioA z x y dx dy *
        ratioB z x y dx dy +
      ratioF22 F z x y * (ratioB z x y dx dy) ^ 2) /
    ((z x y) ^ 2 * ratioDenominator F z x y)

def ratioClosedSecond (F : ℝ → ℝ → ℝ)
    (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  ((y * dx - x * dy) ^ 2 *
      (ratioF11 F z x y * (ratioF2 F z x y) ^ 2 -
        2 * ratioF1 F z x y * ratioF2 F z x y * ratioF12 F z x y +
        ratioF22 F z x y * (ratioF1 F z x y) ^ 2)) /
    (ratioDenominator F z x y) ^ 3

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

private theorem hasDerivAt_comp_uv_along_line
    (f u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (u x y, v x y))
    (hu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    HasDerivAt
      (fun t => f (u (x + t * dx) (y + t * dy))
        (v (x + t * dx) (y + t * dy)))
      (partialX f (u x y) (v x y) * differential u x y dx dy +
        partialY f (u x y) (v x y) * differential v x y dx dy) 0 := by
  have huLine := hasDerivAt_along_line u x y dx dy hu
  have hvLine := hasDerivAt_along_line v x y dx dy hv
  have hp : HasDerivAt
      (fun t => (u (x + t * dx) (y + t * dy),
        v (x + t * dx) (y + t * dy)))
      (differential u x y dx dy, differential v x y dx dy) 0 := by
    convert (huLine.hasFDerivAt.prodMk hvLine.hasFDerivAt).hasDerivAt
      using 1 <;> simp
  have hf0 : HasFDerivAt (Function.uncurry f)
      (fderiv ℝ (Function.uncurry f) (u x y, v x y))
      ((u (x + 0 * dx) (y + 0 * dy), v (x + 0 * dx) (y + 0 * dy))) := by
    simpa using hf.hasFDerivAt
  have hcomp := hf0.comp 0 hp.hasFDerivAt
  convert hcomp.hasDerivAt using 1
  rw [partialX_eq_fderiv f (u x y) (v x y) hf,
    partialY_eq_fderiv f (u x y) (v x y) hf]
  let L := fderiv ℝ (Function.uncurry f) (u x y, v x y)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change
    L (1, 0) * differential u x y dx dy +
        L (0, 1) * differential v x y dx dy =
      L (differential u x y dx dy, differential v x y dx dy)
  rw [show
    (differential u x y dx dy, differential v x y dx dy) =
      differential u x y dx dy • (1, 0) +
        differential v x y dx dy • (0, 1) by ext <;> simp]
  simp only [map_add, map_smul]
  simp [smul_eq_mul]
  ring

private theorem hasDerivAt_comp_uv_at
    (f u v : ℝ → ℝ → ℝ) (x y dx dy t : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f)
      (u (x + t * dx) (y + t * dy), v (x + t * dx) (y + t * dy)))
    (hu : DifferentiableAt ℝ (Function.uncurry u)
      (x + t * dx, y + t * dy))
    (hv : DifferentiableAt ℝ (Function.uncurry v)
      (x + t * dx, y + t * dy)) :
    HasDerivAt
      (fun s => f (u (x + s * dx) (y + s * dy))
        (v (x + s * dx) (y + s * dy)))
      (partialX f (u (x + t * dx) (y + t * dy))
          (v (x + t * dx) (y + t * dy)) *
          differential u (x + t * dx) (y + t * dy) dx dy +
        partialY f (u (x + t * dx) (y + t * dy))
          (v (x + t * dx) (y + t * dy)) *
          differential v (x + t * dx) (y + t * dy) dx dy) t := by
  have huLine := hasDerivAt_along_line_at u x y dx dy t hu
  have hvLine := hasDerivAt_along_line_at v x y dx dy t hv
  have hp : HasDerivAt
      (fun s => (u (x + s * dx) (y + s * dy),
        v (x + s * dx) (y + s * dy)))
      (differential u (x + t * dx) (y + t * dy) dx dy,
        differential v (x + t * dx) (y + t * dy) dx dy) t := by
    convert (huLine.hasFDerivAt.prodMk hvLine.hasFDerivAt).hasDerivAt
      using 1 <;> simp
  have hcomp := hf.hasFDerivAt.comp t hp.hasFDerivAt
  convert hcomp.hasDerivAt using 1
  rw [partialX_eq_fderiv f _ _ hf, partialY_eq_fderiv f _ _ hf]
  let L := fderiv ℝ (Function.uncurry f)
    (u (x + t * dx) (y + t * dy), v (x + t * dx) (y + t * dy))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change L (1, 0) * _ + L (0, 1) * _ = L (_, _)
  rw [show
    (differential u (x + t * dx) (y + t * dy) dx dy,
      differential v (x + t * dx) (y + t * dy) dx dy) =
      differential u (x + t * dx) (y + t * dy) dx dy • (1, 0) +
        differential v (x + t * dx) (y + t * dy) dx dy • (0, 1) by
          ext <;> simp]
  simp only [map_add, map_smul]
  simp [smul_eq_mul]
  ring

private theorem secondDeriv_affine_zero (a da : ℝ) :
    deriv (deriv (fun t => a + t * da)) 0 = 0 := by
  have heq : deriv (fun t => a + t * da) = fun _ => da := by
    funext t
    have ht : HasDerivAt (fun s => a + s * da) da t := by
      convert (hasDerivAt_const t a).add
        ((hasDerivAt_id t).mul_const da) using 1 <;> simp [id]
    exact ht.deriv
  rw [heq]
  simpa using (hasDerivAt_const 0 da).deriv

private theorem second_comp_identity
    (f u v : ℝ → ℝ → ℝ) (lhs : ℝ × ℝ → ℝ) (x y dx dy : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (u x y, v x y))
    (hu : ContDiffAt ℝ 2 (Function.uncurry u) (x, y))
    (hv : ContDiffAt ℝ 2 (Function.uncurry v) (x, y))
    (hEq : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      lhs p = f (u p.1 p.2) (v p.1 p.2))
    (hLhs : deriv (deriv
      (fun t => lhs (x + t * dx, y + t * dy))) 0 = 0) :
    0 = quadratic f (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) +
        partialX f (u x y) (v x y) * secondDifferential u x y dx dy +
        partialY f (u x y) (v x y) * secondDifferential v x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  let w : ℝ → ℝ × ℝ := fun t =>
    (u (x + t * dx) (y + t * dy), v (x + t * dx) (y + t * dy))
  let d : ℝ → ℝ × ℝ := fun t =>
    (differential u (x + t * dx) (y + t * dy) dx dy,
      differential v (x + t * dx) (y + t * dy) dx dy)
  let G := Function.uncurry f
  let L := fderiv ℝ G (u x y, v x y)
  let H := fderiv ℝ (fderiv ℝ G) (u x y, v x y)
  have huLine := hasDerivAt_along_line u x y dx dy
    (hu.differentiableAt (by decide))
  have hvLine := hasDerivAt_along_line v x y dx dy
    (hv.differentiableAt (by decide))
  have huD := hasDerivAt_differential_along_line u x y dx dy hu
  have hvD := hasDerivAt_differential_along_line v x y dx dy hv
  have hw : HasDerivAt w
      (differential u x y dx dy, differential v x y dx dy) 0 := by
    dsimp [w]
    convert (huLine.hasFDerivAt.prodMk hvLine.hasFDerivAt).hasDerivAt
      using 1 <;> simp
  have hd : HasDerivAt d
      (secondDifferential u x y dx dy,
        secondDifferential v x y dx dy) 0 := by
    dsimp [d]
    convert (huD.hasFDerivAt.prodMk hvD.hasFDerivAt).hasDerivAt
      using 1 <;> simp
  have hDfDiff : DifferentiableAt ℝ (fderiv ℝ G) (u x y, v x y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hDf0 : HasFDerivAt (fderiv ℝ G)
      (fderiv ℝ (fderiv ℝ G) (u x y, v x y)) (w 0) := by
    simpa [w] using hDfDiff.hasFDerivAt
  have hDfLine := hDf0.comp 0 hw.hasFDerivAt
  have hR0 := hDfLine.clm_apply hd.hasFDerivAt
  have hR : HasDerivAt
      (fun t => fderiv ℝ G (w t) (d t))
      (H (differential u x y dx dy, differential v x y dx dy)
          (differential u x y dx dy, differential v x y dx dy) +
        L (secondDifferential u x y dx dy,
          secondDifferential v x y dx dy)) 0 := by
    convert hR0.hasDerivAt using 1 <;> simp [H, L, w, d, G] <;> ring
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have hfEv0 : ∀ᶠ p : ℝ × ℝ in nhds (w 0),
      ContDiffAt ℝ 2 (Function.uncurry f) p := by
    simpa [w] using hf.eventually (by simp)
  have hfLine := hw.continuousAt.eventually hfEv0
  have huLineEv := hc.eventually (hu.eventually (by simp))
  have hvLineEv := hc.eventually (hv.eventually (by simp))
  have hDeriv :
      deriv
          (fun t => f (u (x + t * dx) (y + t * dy))
            (v (x + t * dx) (y + t * dy))) =ᶠ[nhds 0]
        (fun t => fderiv ℝ G (w t) (d t)) := by
    filter_upwards [hfLine, huLineEv, hvLineEv] with t hft hut hvt
    rw [(hasDerivAt_comp_uv_at f u v x y dx dy t
      (hft.differentiableAt (by decide))
      (hut.differentiableAt (by decide))
      (hvt.differentiableAt (by decide))).deriv]
    rw [partialX_eq_fderiv f _ _
      (hft.differentiableAt (by decide))]
    rw [partialY_eq_fderiv f _ _
      (hft.differentiableAt (by decide))]
    dsimp [G, w, d]
    rw [show
      (differential u (x + t * dx) (y + t * dy) dx dy,
        differential v (x + t * dx) (y + t * dy) dx dy) =
        differential u (x + t * dx) (y + t * dy) dx dy • (1, 0) +
          differential v (x + t * dx) (y + t * dy) dx dy • (0, 1) by
            ext <;> simp]
    simp only [map_add, map_smul]
    simp [smul_eq_mul]
    ring
  have he := Filter.EventuallyEq.comp_tendsto hEq hc
  have hDerivEq := he.deriv
  have hSecond :
      deriv
          (deriv
            (fun t => f (u (x + t * dx) (y + t * dy))
              (v (x + t * dx) (y + t * dy)))) 0 =
        H (differential u x y dx dy, differential v x y dx dy)
            (differential u x y dx dy, differential v x y dx dy) +
          L (secondDifferential u x y dx dy,
            secondDifferential v x y dx dy) := by
    have hh := Filter.EventuallyEq.deriv_eq hDeriv
    rw [hR.deriv] at hh
    exact hh
  have hZero :
      0 = deriv
          (deriv
            (fun t => f (u (x + t * dx) (y + t * dy))
              (v (x + t * dx) (y + t * dy)))) 0 := by
    have hh := Filter.EventuallyEq.deriv_eq hDerivEq
    have hh' :
        deriv (deriv (fun t => lhs (x + t * dx, y + t * dy))) 0 =
          deriv
            (deriv
              (fun t => f (u (x + t * dx) (y + t * dy))
                (v (x + t * dx) (y + t * dy)))) 0 := by
      simpa [Function.comp_def, c] using hh
    rw [hLhs] at hh'
    exact hh'
  rw [hSecond] at hZero
  have hQuad :
      quadratic f (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) =
        H (differential u x y dx dy, differential v x y dx dy)
          (differential u x y dx dy, differential v x y dx dy) := by
    unfold quadratic
    simpa [H, G] using
      secondDifferential_eq_sndFDeriv f (u x y) (v x y)
        (differential u x y dx dy) (differential v x y dx dy) hf
  rw [hQuad]
  rw [partialX_eq_fderiv f _ _ (hf.differentiableAt (by decide)),
    partialY_eq_fderiv f _ _ (hf.differentiableAt (by decide))]
  convert hZero using 1
  rw [show
    (secondDifferential u x y dx dy, secondDifferential v x y dx dy) =
      secondDifferential u x y dx dy • (1, 0) +
        secondDifferential v x y dx dy • (0, 1) by ext <;> simp]
  simp only [map_add, map_smul]
  simp [L, smul_eq_mul]
  ring

private theorem hasDerivAt_outer_pair
    (F : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (t a' b' : ℝ)
    (hF : DifferentiableAt ℝ (Function.uncurry F) (a t, b t))
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => F (a s) (b s))
      (partialX F (a t) (b t) * a' + partialY F (a t) (b t) * b') t := by
  have hp : HasDerivAt (fun s => (a s, b s)) (a', b') t := by
    convert (ha.hasFDerivAt.prodMk hb.hasFDerivAt).hasDerivAt using 1 <;>
      simp
  have hcomp := hF.hasFDerivAt.comp t hp.hasFDerivAt
  convert hcomp.hasDerivAt using 1
  rw [partialX_eq_fderiv F _ _ hF, partialY_eq_fderiv F _ _ hF]
  let L := fderiv ℝ (Function.uncurry F) (a t, b t)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change L (1, 0) * a' + L (0, 1) * b' = L (a', b')
  rw [show (a', b') = a' • (1, 0) + b' • (0, 1) by ext <;> simp]
  simp only [map_add, map_smul]
  simp [smul_eq_mul]
  ring

theorem gap1 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hFDiff :
      DifferentiableAt ℝ (Function.uncurry F)
        (plusArg1 z x y, plusArg2 z x y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hPlus :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (plusArg1 z p.1 p.2) (plusArg2 z p.1 p.2) = 0) :
    plusF1 F z x y * (dx + differential z x y dx dy) +
      plusF2 F z x y * (dy + differential z x y dx dy) = 0 := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have hzLine := hasDerivAt_along_line z x y dx dy hzDiff
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have ha := hxLine.add hzLine
  have hb := hyLine.add hzLine
  have hout := hasDerivAt_outer_pair F
    (fun t => x + t * dx + z (x + t * dx) (y + t * dy))
    (fun t => y + t * dy + z (x + t * dx) (y + t * dy))
    0 (dx + differential z x y dx dy)
    (dy + differential z x y dx dy)
    (by simpa [plusArg1, plusArg2] using hFDiff) ha hb
  have he := Filter.EventuallyEq.comp_tendsto hPlus hc
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv
          (fun t => F
            (x + t * dx + z (x + t * dx) (y + t * dy))
            (y + t * dy + z (x + t * dx) (y + t * dy))) 0 =
        deriv (fun _ : ℝ => 0) 0 := by
    simpa [c, Function.comp_def, plusArg1, plusArg2] using hd
  rw [hout.deriv] at hd'
  simpa [plusF1, plusF2, evalPlus, plusArg1, plusArg2] using hd'

theorem gap2 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hDenominator : plusF1 F z x y + plusF2 F z x y ≠ 0)
    (hFirst :
      plusF1 F z x y * (dx + differential z x y dx dy) +
        plusF2 F z x y * (dy + differential z x y dx dy) = 0) :
    differential z x y dx dy =
      plusSolvedDifferential F z x y dx dy := by
  unfold plusSolvedDifferential
  rw [eq_div_iff hDenominator]
  linear_combination hFirst

theorem gap3 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hDenominator : plusF1 F z x y + plusF2 F z x y ≠ 0)
    (hFirst :
      differential z x y dx dy =
        plusSolvedDifferential F z x y dx dy) :
    dx + differential z x y dx dy =
      plusF2 F z x y * (dx - dy) /
        (plusF1 F z x y + plusF2 F z x y) := by
  rw [hFirst]
  unfold plusSolvedDifferential
  field_simp [hDenominator]
  ring

theorem gap4 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hDenominator : plusF1 F z x y + plusF2 F z x y ≠ 0)
    (hFirst :
      differential z x y dx dy =
        plusSolvedDifferential F z x y dx dy) :
    dy + differential z x y dx dy =
      -(plusF1 F z x y * (dx - dy)) /
        (plusF1 F z x y + plusF2 F z x y) := by
  rw [hFirst]
  unfold plusSolvedDifferential
  field_simp [hDenominator]
  ring

theorem gap5 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hFC2 :
      ContDiffAt ℝ 2 (Function.uncurry F)
        (plusArg1 z x y, plusArg2 z x y))
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hPlus :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (plusArg1 z p.1 p.2) (plusArg2 z p.1 p.2) = 0) :
    plusF11 F z x y * (dx + differential z x y dx dy) ^ 2 +
        2 * plusF12 F z x y * (dx + differential z x y dx dy) *
          (dy + differential z x y dx dy) +
        plusF22 F z x y * (dy + differential z x y dx dy) ^ 2 +
        (plusF1 F z x y + plusF2 F z x y) *
          secondDifferential z x y dx dy = 0 := by
  let P : ℝ → ℝ → ℝ := fun a b => a + z a b
  let Q : ℝ → ℝ → ℝ := fun a b => b + z a b
  have hPC2 : ContDiffAt ℝ 2 (Function.uncurry P) (x, y) := by
    dsimp [P, Function.uncurry]
    fun_prop
  have hQC2 : ContDiffAt ℝ 2 (Function.uncurry Q) (x, y) := by
    dsimp [Q, Function.uncurry]
    fun_prop
  have hPLine := hasDerivAt_along_line P x y dx dy
    (hPC2.differentiableAt (by decide))
  have hQLine := hasDerivAt_along_line Q x y dx dy
    (hQC2.differentiableAt (by decide))
  have hzLine := hasDerivAt_along_line z x y dx dy
    (hzC2.differentiableAt (by decide))
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hDP : differential P x y dx dy =
      dx + differential z x y dx dy := by
    exact hPLine.unique (by simpa [P] using hxLine.add hzLine)
  have hDQ : differential Q x y dx dy =
      dy + differential z x y dx dy := by
    exact hQLine.unique (by simpa [Q] using hyLine.add hzLine)
  have hzD := hasDerivAt_differential_along_line z x y dx dy hzC2
  have hPD := hasDerivAt_differential_along_line P x y dx dy hPC2
  have hQD := hasDerivAt_differential_along_line Q x y dx dy hQC2
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have hzEv := hc.eventually (hzC2.eventually (by simp))
  have hDPEv :
      (fun t => differential P (x + t * dx) (y + t * dy) dx dy) =ᶠ[nhds 0]
        (fun t => dx + differential z (x + t * dx) (y + t * dy) dx dy) := by
    filter_upwards [hzEv] with t hzt
    have hzT := hasDerivAt_along_line_at z x y dx dy t
      (hzt.differentiableAt (by decide))
    have hxT : HasDerivAt (fun s => x + s * dx) dx t := by
      convert (hasDerivAt_const t x).add
        ((hasDerivAt_id t).mul_const dx) using 1 <;> simp [id]
    have hPT := hasDerivAt_along_line_at P x y dx dy t (by
      have hztd := hzt.differentiableAt (by decide)
      dsimp [P, Function.uncurry]
      fun_prop)
    exact hPT.unique (by simpa [P] using hxT.add hzT)
  have hDQEv :
      (fun t => differential Q (x + t * dx) (y + t * dy) dx dy) =ᶠ[nhds 0]
        (fun t => dy + differential z (x + t * dx) (y + t * dy) dx dy) := by
    filter_upwards [hzEv] with t hzt
    have hzT := hasDerivAt_along_line_at z x y dx dy t
      (hzt.differentiableAt (by decide))
    have hyT : HasDerivAt (fun s => y + s * dy) dy t := by
      convert (hasDerivAt_const t y).add
        ((hasDerivAt_id t).mul_const dy) using 1 <;> simp [id]
    have hQT := hasDerivAt_along_line_at Q x y dx dy t (by
      have hztd := hzt.differentiableAt (by decide)
      dsimp [Q, Function.uncurry]
      fun_prop)
    exact hQT.unique (by simpa [Q] using hyT.add hzT)
  have hD2P : secondDifferential P x y dx dy =
      secondDifferential z x y dx dy := by
    have hd := Filter.EventuallyEq.deriv_eq hDPEv
    rw [hPD.deriv] at hd
    have hr := (hasDerivAt_const 0 dx).add hzD
    have hr' : HasDerivAt
        (fun t => dx + differential z (x + t * dx) (y + t * dy) dx dy)
        (secondDifferential z x y dx dy) 0 := by
      convert hr using 1 <;> simp
    rw [hr'.deriv] at hd
    exact hd
  have hD2Q : secondDifferential Q x y dx dy =
      secondDifferential z x y dx dy := by
    have hd := Filter.EventuallyEq.deriv_eq hDQEv
    rw [hQD.deriv] at hd
    have hr := (hasDerivAt_const 0 dy).add hzD
    have hr' : HasDerivAt
        (fun t => dy + differential z (x + t * dx) (y + t * dy) dx dy)
        (secondDifferential z x y dx dy) 0 := by
      convert hr using 1 <;> simp
    rw [hr'.deriv] at hd
    exact hd
  have hgen := second_comp_identity F P Q (fun _ => 0) x y dx dy
    (by simpa [P, Q, plusArg1, plusArg2] using hFC2)
    hPC2 hQC2
    (by simpa [P, Q, plusArg1, plusArg2] using
      Filter.EventuallyEq.symm hPlus)
    (by simpa using secondDeriv_affine_zero 0 0)
  rw [hDP, hDQ, hD2P, hD2Q] at hgen
  dsimp [P, Q] at hgen
  unfold quadratic at hgen
  change
    partialXX F (x + z x y) (y + z x y) *
          (dx + differential z x y dx dy) ^ 2 +
        2 * partialXY F (x + z x y) (y + z x y) *
          (dx + differential z x y dx dy) *
          (dy + differential z x y dx dy) +
        partialYY F (x + z x y) (y + z x y) *
          (dy + differential z x y dx dy) ^ 2 +
        (partialX F (x + z x y) (y + z x y) +
          partialY F (x + z x y) (y + z x y)) *
          secondDifferential z x y dx dy = 0
  linear_combination -hgen

theorem gap6 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hDenominator : plusF1 F z x y + plusF2 F z x y ≠ 0)
    (hSecond :
      plusF11 F z x y * (dx + differential z x y dx dy) ^ 2 +
          2 * plusF12 F z x y * (dx + differential z x y dx dy) *
            (dy + differential z x y dx dy) +
          plusF22 F z x y * (dy + differential z x y dx dy) ^ 2 +
          (plusF1 F z x y + plusF2 F z x y) *
            secondDifferential z x y dx dy = 0) :
    secondDifferential z x y dx dy =
      plusRawSecond F z x y dx dy := by
  unfold plusRawSecond
  rw [eq_div_iff hDenominator]
  linear_combination hSecond

theorem gap7 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hDenominator : plusF1 F z x y + plusF2 F z x y ≠ 0)
    (hDx :
      dx + differential z x y dx dy =
        plusF2 F z x y * (dx - dy) /
          (plusF1 F z x y + plusF2 F z x y))
    (hDy :
      dy + differential z x y dx dy =
        -(plusF1 F z x y * (dx - dy)) /
          (plusF1 F z x y + plusF2 F z x y))
    (hRaw :
      secondDifferential z x y dx dy =
        plusRawSecond F z x y dx dy) :
    secondDifferential z x y dx dy =
      plusClosedSecond F z x y dx dy := by
  rw [hRaw]
  unfold plusRawSecond plusClosedSecond
  rw [hDx, hDy]
  field_simp [hDenominator]
  ring

theorem gap8 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hz : z x y ≠ 0)
    (hFDiff :
      DifferentiableAt ℝ (Function.uncurry F)
        (ratioArg1 z x y, ratioArg2 z x y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hRatio :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (ratioArg1 z p.1 p.2) (ratioArg2 z p.1 p.2) = 0) :
    ratioF1 F z x y * (ratioA z x y dx dy / (z x y) ^ 2) +
      ratioF2 F z x y * (ratioB z x y dx dy / (z x y) ^ 2) = 0 := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have hzLine := hasDerivAt_along_line z x y dx dy hzDiff
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hz0 : z (x + 0 * dx) (y + 0 * dy) ≠ 0 := by simpa using hz
  have ha : HasDerivAt
      (fun t => (x + t * dx) / z (x + t * dx) (y + t * dy))
      (ratioA z x y dx dy / (z x y) ^ 2) 0 := by
    convert hxLine.div hzLine hz0 using 1 <;>
      simp [ratioA] <;> field_simp [hz] <;> ring
  have hb : HasDerivAt
      (fun t => (y + t * dy) / z (x + t * dx) (y + t * dy))
      (ratioB z x y dx dy / (z x y) ^ 2) 0 := by
    convert hyLine.div hzLine hz0 using 1 <;>
      simp [ratioB] <;> field_simp [hz] <;> ring
  have hout := hasDerivAt_outer_pair F
    (fun t => (x + t * dx) / z (x + t * dx) (y + t * dy))
    (fun t => (y + t * dy) / z (x + t * dx) (y + t * dy))
    0 (ratioA z x y dx dy / (z x y) ^ 2)
    (ratioB z x y dx dy / (z x y) ^ 2)
    (by simpa [ratioArg1, ratioArg2] using hFDiff) ha hb
  have he := Filter.EventuallyEq.comp_tendsto hRatio hc
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv
          (fun t => F
            ((x + t * dx) / z (x + t * dx) (y + t * dy))
            ((y + t * dy) / z (x + t * dx) (y + t * dy))) 0 =
        deriv (fun _ : ℝ => 0) 0 := by
    simpa [c, Function.comp_def, ratioArg1, ratioArg2] using hd
  rw [hout.deriv] at hd'
  simpa [ratioF1, ratioF2, evalRatio, ratioArg1, ratioArg2] using hd'

theorem gap9 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hz : z x y ≠ 0)
    (hDenominator : ratioDenominator F z x y ≠ 0)
    (hFirst :
      ratioF1 F z x y * (ratioA z x y dx dy / (z x y) ^ 2) +
        ratioF2 F z x y * (ratioB z x y dx dy / (z x y) ^ 2) = 0) :
    differential z x y dx dy =
      ratioSolvedDifferential F z x y dx dy := by
  have hFirst' :
      ratioF1 F z x y * ratioA z x y dx dy +
        ratioF2 F z x y * ratioB z x y dx dy = 0 := by
    field_simp [hz] at hFirst
    simpa using hFirst
  unfold ratioSolvedDifferential
  rw [eq_div_iff hDenominator]
  unfold ratioA ratioB at hFirst'
  unfold ratioDenominator
  linear_combination -hFirst'

theorem gap10 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hDenominator : ratioDenominator F z x y ≠ 0)
    (hFirst :
      differential z x y dx dy =
        ratioSolvedDifferential F z x y dx dy) :
    ratioA z x y dx dy =
      z x y * ratioF2 F z x y * (y * dx - x * dy) /
        ratioDenominator F z x y := by
  unfold ratioA
  rw [hFirst]
  unfold ratioSolvedDifferential
  rw [eq_div_iff hDenominator]
  field_simp [hDenominator]
  unfold ratioDenominator
  ring

theorem gap11 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hDenominator : ratioDenominator F z x y ≠ 0)
    (hFirst :
      differential z x y dx dy =
        ratioSolvedDifferential F z x y dx dy) :
    ratioB z x y dx dy =
      -(z x y * ratioF1 F z x y * (y * dx - x * dy)) /
        ratioDenominator F z x y := by
  unfold ratioB
  rw [hFirst]
  unfold ratioSolvedDifferential
  rw [eq_div_iff hDenominator]
  field_simp [hDenominator]
  unfold ratioDenominator
  ring

theorem gap12 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hz : z x y ≠ 0)
    (hFC2 :
      ContDiffAt ℝ 2 (Function.uncurry F)
        (ratioArg1 z x y, ratioArg2 z x y))
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hRatio :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (ratioArg1 z p.1 p.2) (ratioArg2 z p.1 p.2) = 0) :
    ratioF11 F z x y * (ratioA z x y dx dy) ^ 2 / (z x y) ^ 2 +
        2 * ratioF12 F z x y * ratioA z x y dx dy *
          ratioB z x y dx dy / (z x y) ^ 2 +
        ratioF22 F z x y * (ratioB z x y dx dy) ^ 2 / (z x y) ^ 2 -
        ratioDenominator F z x y * secondDifferential z x y dx dy = 0 := by
  let R : ℝ → ℝ → ℝ := fun a b => a / z a b
  let S : ℝ → ℝ → ℝ := fun a b => b / z a b
  have hRC2 : ContDiffAt ℝ 2 (Function.uncurry R) (x, y) := by
    change ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => p.1 / z p.1 p.2) (x, y)
    exact contDiffAt_fst.div hzC2 hz
  have hSC2 : ContDiffAt ℝ 2 (Function.uncurry S) (x, y) := by
    change ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => p.2 / z p.1 p.2) (x, y)
    exact contDiffAt_snd.div hzC2 hz
  have hzDiff := hzC2.differentiableAt (by decide)
  have hzLine := hasDerivAt_along_line z x y dx dy hzDiff
  have hzD := hasDerivAt_differential_along_line z x y dx dy hzC2
  have hxLine : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hyLine : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hz0 : z (x + 0 * dx) (y + 0 * dy) ≠ 0 := by simpa using hz
  have hRLine := hasDerivAt_along_line R x y dx dy
    (hRC2.differentiableAt (by decide))
  have hSLine := hasDerivAt_along_line S x y dx dy
    (hSC2.differentiableAt (by decide))
  have hDR : differential R x y dx dy =
      ratioA z x y dx dy / (z x y) ^ 2 := by
    exact hRLine.unique (by
      convert hxLine.div hzLine hz0 using 1 <;>
        simp [R, ratioA] <;> field_simp [hz] <;> ring)
  have hDS : differential S x y dx dy =
      ratioB z x y dx dy / (z x y) ^ 2 := by
    exact hSLine.unique (by
      convert hyLine.div hzLine hz0 using 1 <;>
        simp [S, ratioB] <;> field_simp [hz] <;> ring)
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have hzC2Ev :
      ∀ᶠ t : ℝ in nhds 0,
        ContDiffAt ℝ 2 (Function.uncurry z)
          (x + t * dx, y + t * dy) := by
    simpa [c] using hc.eventually (hzC2.eventually (by simp))
  have hzNeEv :
      ∀ᶠ t : ℝ in nhds 0, z (x + t * dx) (y + t * dy) ≠ 0 := by
    exact hzLine.continuousAt.eventually_ne hz0
  have hDREv :
      (fun t => differential R (x + t * dx) (y + t * dy) dx dy)
          =ᶠ[nhds 0]
        (fun t =>
          (z (x + t * dx) (y + t * dy) * dx -
              (x + t * dx) *
                differential z (x + t * dx) (y + t * dy) dx dy) /
            z (x + t * dx) (y + t * dy) ^ 2) := by
    filter_upwards [hzC2Ev, hzNeEv] with t hzt hzne
    have hzT := hasDerivAt_along_line_at z x y dx dy t
      (hzt.differentiableAt (by decide))
    have hxT : HasDerivAt (fun s => x + s * dx) dx t := by
      convert (hasDerivAt_const t x).add
        ((hasDerivAt_id t).mul_const dx) using 1 <;> simp [id]
    have hRT := hasDerivAt_along_line_at R x y dx dy t (by
      change DifferentiableAt ℝ
        (fun p : ℝ × ℝ => p.1 / z p.1 p.2)
        (x + t * dx, y + t * dy)
      have hfst : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1)
          (x + t * dx, y + t * dy) := differentiableAt_fst
      have hztd : DifferentiableAt ℝ
          (fun p : ℝ × ℝ => z p.1 p.2)
          (x + t * dx, y + t * dy) := by
        simpa [Function.uncurry] using hzt.differentiableAt (by decide)
      simpa [div_eq_mul_inv] using hfst.mul (hztd.inv hzne))
    exact hRT.unique (by
      have hq := hxT.div hzT hzne
      convert hq using 1 <;> ring)
  have hDSEv :
      (fun t => differential S (x + t * dx) (y + t * dy) dx dy)
          =ᶠ[nhds 0]
        (fun t =>
          (z (x + t * dx) (y + t * dy) * dy -
              (y + t * dy) *
                differential z (x + t * dx) (y + t * dy) dx dy) /
            z (x + t * dx) (y + t * dy) ^ 2) := by
    filter_upwards [hzC2Ev, hzNeEv] with t hzt hzne
    have hzT := hasDerivAt_along_line_at z x y dx dy t
      (hzt.differentiableAt (by decide))
    have hyT : HasDerivAt (fun s => y + s * dy) dy t := by
      convert (hasDerivAt_const t y).add
        ((hasDerivAt_id t).mul_const dy) using 1 <;> simp [id]
    have hST := hasDerivAt_along_line_at S x y dx dy t (by
      change DifferentiableAt ℝ
        (fun p : ℝ × ℝ => p.2 / z p.1 p.2)
        (x + t * dx, y + t * dy)
      have hsnd : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.2)
          (x + t * dx, y + t * dy) := differentiableAt_snd
      have hztd : DifferentiableAt ℝ
          (fun p : ℝ × ℝ => z p.1 p.2)
          (x + t * dx, y + t * dy) := by
        simpa [Function.uncurry] using hzt.differentiableAt (by decide)
      simpa [div_eq_mul_inv] using hsnd.mul (hztd.inv hzne))
    exact hST.unique (by
      have hq := hyT.div hzT hzne
      convert hq using 1 <;> ring)
  have hRD := hasDerivAt_differential_along_line R x y dx dy hRC2
  have hSD := hasDerivAt_differential_along_line S x y dx dy hSC2
  have hRightR : HasDerivAt
      (fun t =>
        (z (x + t * dx) (y + t * dy) * dx -
            (x + t * dx) *
              differential z (x + t * dx) (y + t * dy) dx dy) /
          z (x + t * dx) (y + t * dy) ^ 2)
      (-(x * secondDifferential z x y dx dy * z x y +
          2 * ratioA z x y dx dy * differential z x y dx dy) /
        (z x y) ^ 3) 0 := by
    have hnum := (hzLine.mul_const dx).sub (hxLine.mul hzD)
    have hden := hzLine.pow 2
    convert hnum.div hden (by simpa using pow_ne_zero 2 hz) using 1 <;>
      simp [ratioA] <;> field_simp [hz] <;> ring
  have hRightS : HasDerivAt
      (fun t =>
        (z (x + t * dx) (y + t * dy) * dy -
            (y + t * dy) *
              differential z (x + t * dx) (y + t * dy) dx dy) /
          z (x + t * dx) (y + t * dy) ^ 2)
      (-(y * secondDifferential z x y dx dy * z x y +
          2 * ratioB z x y dx dy * differential z x y dx dy) /
        (z x y) ^ 3) 0 := by
    have hnum := (hzLine.mul_const dy).sub (hyLine.mul hzD)
    have hden := hzLine.pow 2
    convert hnum.div hden (by simpa using pow_ne_zero 2 hz) using 1 <;>
      simp [ratioB] <;> field_simp [hz] <;> ring
  have hD2R : secondDifferential R x y dx dy =
      -(x * secondDifferential z x y dx dy * z x y +
          2 * ratioA z x y dx dy * differential z x y dx dy) /
        (z x y) ^ 3 := by
    have hd := Filter.EventuallyEq.deriv_eq hDREv
    rw [hRD.deriv, hRightR.deriv] at hd
    exact hd
  have hD2S : secondDifferential S x y dx dy =
      -(y * secondDifferential z x y dx dy * z x y +
          2 * ratioB z x y dx dy * differential z x y dx dy) /
        (z x y) ^ 3 := by
    have hd := Filter.EventuallyEq.deriv_eq hDSEv
    rw [hSD.deriv, hRightS.deriv] at hd
    exact hd
  have hFirst := gap8 F z x y dx dy hz
    (hFC2.differentiableAt (by decide)) hzDiff hRatio
  have hFirst' :
      ratioF1 F z x y * ratioA z x y dx dy +
        ratioF2 F z x y * ratioB z x y dx dy = 0 := by
    field_simp [hz] at hFirst
    simpa using hFirst
  have hgen := second_comp_identity F R S (fun _ => 0) x y dx dy
    (by simpa [R, S, ratioArg1, ratioArg2] using hFC2)
    hRC2 hSC2
    (by simpa [R, S, ratioArg1, ratioArg2] using
      Filter.EventuallyEq.symm hRatio)
    (by simpa using secondDeriv_affine_zero 0 0)
  rw [hDR, hDS, hD2R, hD2S] at hgen
  dsimp [R, S] at hgen
  unfold quadratic at hgen
  simp only [ratioF1, ratioF2, ratioF11, ratioF12, ratioF22,
    evalRatio, ratioArg1, ratioArg2, ratioDenominator] at hFirst' ⊢
  simp only [partial1, partial2, partial11, partial12, partial22,
    partialX, partialY, partialXX, partialXY, partialYY] at hFirst' hgen ⊢
  field_simp [hz] at hgen ⊢
  linear_combination -hgen +
    (2 * differential z x y dx dy * z x y) * hFirst'

theorem gap13 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hz : z x y ≠ 0)
    (hDenominator : ratioDenominator F z x y ≠ 0)
    (hSecond :
      ratioF11 F z x y * (ratioA z x y dx dy) ^ 2 / (z x y) ^ 2 +
          2 * ratioF12 F z x y * ratioA z x y dx dy *
            ratioB z x y dx dy / (z x y) ^ 2 +
          ratioF22 F z x y * (ratioB z x y dx dy) ^ 2 / (z x y) ^ 2 -
          ratioDenominator F z x y * secondDifferential z x y dx dy = 0) :
    secondDifferential z x y dx dy =
      ratioRawSecond F z x y dx dy := by
  unfold ratioRawSecond
  rw [eq_div_iff]
  · field_simp [hz] at hSecond ⊢
    linear_combination -hSecond
  · exact mul_ne_zero (pow_ne_zero 2 hz) hDenominator

theorem gap14 (F : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hz : z x y ≠ 0)
    (hDenominator : ratioDenominator F z x y ≠ 0)
    (hA :
      ratioA z x y dx dy =
        z x y * ratioF2 F z x y * (y * dx - x * dy) /
          ratioDenominator F z x y)
    (hB :
      ratioB z x y dx dy =
        -(z x y * ratioF1 F z x y * (y * dx - x * dy)) /
          ratioDenominator F z x y)
    (hRaw :
      secondDifferential z x y dx dy =
        ratioRawSecond F z x y dx dy) :
    secondDifferential z x y dx dy =
      ratioClosedSecond F z x y dx dy := by
  rw [hRaw]
  unfold ratioRawSecond ratioClosedSecond
  rw [hA, hB]
  field_simp [hz, hDenominator]
  ring

end

end ProofGap.Exercise3399
