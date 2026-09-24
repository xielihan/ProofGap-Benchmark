import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3414

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def quadratic (f : ℝ → ℝ → ℝ) (a b da db : ℝ) : ℝ :=
  partialXX f a b * da ^ 2 +
    2 * partialXY f a b * da * db +
    partialYY f a b * db ^ 2

def phiU (φ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX φ (u x y) (v x y)

def phiV (φ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY φ (u x y) (v x y)

def psiU (ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX ψ (u x y) (v x y)

def psiV (ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY ψ (u x y) (v x y)

def jacobian (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  phiU φ u v x y * psiV ψ u v x y -
    phiV φ u v x y * psiU ψ u v x y

def firstNumeratorU (φ ψ u v : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  psiV ψ u v x y * dx - phiV φ u v x y * dy

def firstNumeratorV (φ ψ u v : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  phiU φ u v x y * dy - psiU ψ u v x y * dx

def inverseSecondU (φ ψ u v : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  let a := u x y
  let b := v x y
  let A := firstNumeratorU φ ψ u v x y dx dy
  let B := firstNumeratorV φ ψ u v x y dx dy
  let c11 := phiV φ u v x y * partialXX ψ a b -
    psiV ψ u v x y * partialXX φ a b
  let c12 := phiV φ u v x y * partialXY ψ a b -
    psiV ψ u v x y * partialXY φ a b
  let c22 := phiV φ u v x y * partialYY ψ a b -
    psiV ψ u v x y * partialYY φ a b
  (c11 * A ^ 2 + 2 * c12 * A * B + c22 * B ^ 2) /
    (jacobian φ ψ u v x y) ^ 3

def inverseUxx (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ((phiV φ u v x y * partialXX ψ (u x y) (v x y) -
      psiV ψ u v x y * partialXX φ (u x y) (v x y)) *
      (psiV ψ u v x y) ^ 2 -
    2 * (phiV φ u v x y * partialXY ψ (u x y) (v x y) -
      psiV ψ u v x y * partialXY φ (u x y) (v x y)) *
      psiU ψ u v x y * psiV ψ u v x y +
    (phiV φ u v x y * partialYY ψ (u x y) (v x y) -
      psiV ψ u v x y * partialYY φ (u x y) (v x y)) *
      (psiU ψ u v x y) ^ 2) /
    (jacobian φ ψ u v x y) ^ 3

def inverseUxy (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ((psiV ψ u v x y * partialXX φ (u x y) (v x y) -
      phiV φ u v x y * partialXX ψ (u x y) (v x y)) *
      psiV ψ u v x y * phiV φ u v x y -
    (psiV ψ u v x y * partialXY φ (u x y) (v x y) -
      phiV φ u v x y * partialXY ψ (u x y) (v x y)) *
      (phiU φ u v x y * psiV ψ u v x y +
        phiV φ u v x y * psiU ψ u v x y) +
    (psiV ψ u v x y * partialYY φ (u x y) (v x y) -
      phiV φ u v x y * partialYY ψ (u x y) (v x y)) *
      phiU φ u v x y * psiU ψ u v x y) /
    (jacobian φ ψ u v x y) ^ 3

def inverseUyy (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ((phiV φ u v x y * partialXX ψ (u x y) (v x y) -
      psiV ψ u v x y * partialXX φ (u x y) (v x y)) *
      (phiV φ u v x y) ^ 2 -
    2 * (phiV φ u v x y * partialXY ψ (u x y) (v x y) -
      psiV ψ u v x y * partialXY φ (u x y) (v x y)) *
      phiU φ u v x y * phiV φ u v x y +
    (phiV φ u v x y * partialYY ψ (u x y) (v x y) -
      psiV ψ u v x y * partialYY φ (u x y) (v x y)) *
      (phiU φ u v x y) ^ 2) /
    (jacobian φ ψ u v x y) ^ 3

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

theorem gap1 (φ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hφDiff : DifferentiableAt ℝ (Function.uncurry φ) (u x y, v x y))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = φ (u p.1 p.2) (v p.1 p.2)) :
    dx = phiU φ u v x y * differential u x y dx dy +
      phiV φ u v x y * differential v x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hX hc
  have hl : HasDerivAt (fun t => x + t * dx) dx 0 := by
    convert (hasDerivAt_const 0 x).add
      ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hr := hasDerivAt_comp_uv_along_line φ u v x y dx dy
    hφDiff huDiff hvDiff
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv (fun t => x + t * dx) 0 =
        deriv (fun t => φ (u (x + t * dx) (y + t * dy))
          (v (x + t * dx) (y + t * dy))) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hl.deriv, hr.deriv] at hd'
  simpa [phiU, phiV] using hd'

theorem gap2 (ψ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hψDiff : DifferentiableAt ℝ (Function.uncurry ψ) (u x y, v x y))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = ψ (u p.1 p.2) (v p.1 p.2)) :
    dy = psiU ψ u v x y * differential u x y dx dy +
      psiV ψ u v x y * differential v x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hY hc
  have hl : HasDerivAt (fun t => y + t * dy) dy 0 := by
    convert (hasDerivAt_const 0 y).add
      ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hr := hasDerivAt_comp_uv_along_line ψ u v x y dx dy
    hψDiff huDiff hvDiff
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv (fun t => y + t * dy) 0 =
        deriv (fun t => ψ (u (x + t * dx) (y + t * dy))
          (v (x + t * dx) (y + t * dy))) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hl.deriv, hr.deriv] at hd'
  simpa [psiU, psiV] using hd'

theorem gap3 (φ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hφC2 : ContDiffAt ℝ 2 (Function.uncurry φ) (u x y, v x y))
    (huC2 : ContDiffAt ℝ 2 (Function.uncurry u) (x, y))
    (hvC2 : ContDiffAt ℝ 2 (Function.uncurry v) (x, y))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = φ (u p.1 p.2) (v p.1 p.2)) :
    0 = quadratic φ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) +
        phiU φ u v x y * secondDifferential u x y dx dy +
        phiV φ u v x y * secondDifferential v x y dx dy := by
  simpa [phiU, phiV] using
    second_comp_identity φ u v (fun p => p.1) x y dx dy
      hφC2 huC2 hvC2 hX (secondDeriv_affine_zero x dx)

theorem gap4 (ψ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hψC2 : ContDiffAt ℝ 2 (Function.uncurry ψ) (u x y, v x y))
    (huC2 : ContDiffAt ℝ 2 (Function.uncurry u) (x, y))
    (hvC2 : ContDiffAt ℝ 2 (Function.uncurry v) (x, y))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = ψ (u p.1 p.2) (v p.1 p.2)) :
    0 = quadratic ψ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) +
        psiU ψ u v x y * secondDifferential u x y dx dy +
        psiV ψ u v x y * secondDifferential v x y dx dy := by
  simpa [psiU, psiV] using
    second_comp_identity ψ u v (fun p => p.2) x y dx dy
      hψC2 huC2 hvC2 hY (secondDeriv_affine_zero y dy)

theorem gap5 (φ ψ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hX : dx = phiU φ u v x y * differential u x y dx dy +
      phiV φ u v x y * differential v x y dx dy)
    (hY : dy = psiU ψ u v x y * differential u x y dx dy +
      psiV ψ u v x y * differential v x y dx dy) :
    differential u x y dx dy =
      firstNumeratorU φ ψ u v x y dx dy / jacobian φ ψ u v x y := by
  rw [eq_div_iff hJac]
  unfold firstNumeratorU jacobian
  linear_combination -psiV ψ u v x y * hX + phiV φ u v x y * hY

theorem gap6 (φ ψ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hX : dx = phiU φ u v x y * differential u x y dx dy +
      phiV φ u v x y * differential v x y dx dy)
    (hY : dy = psiU ψ u v x y * differential u x y dx dy +
      psiV ψ u v x y * differential v x y dx dy) :
    differential v x y dx dy =
      firstNumeratorV φ ψ u v x y dx dy / jacobian φ ψ u v x y := by
  rw [eq_div_iff hJac]
  unfold firstNumeratorV jacobian
  linear_combination psiU ψ u v x y * hX - phiU φ u v x y * hY

theorem gap7 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hGeneral : differential u x y 1 0 =
      firstNumeratorU φ ψ u v x y 1 0 / jacobian φ ψ u v x y) :
    partialX u x y = psiV ψ u v x y / jacobian φ ψ u v x y := by
  simpa [differential, firstNumeratorU] using hGeneral

theorem gap8 (ψ u v : ℝ → ℝ → ℝ) (I x y : ℝ) :
    psiV ψ u v x y / I =
      partialY ψ (u x y) (v x y) / I := by rfl

theorem gap9 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (h1 : partialX u x y = psiV ψ u v x y / jacobian φ ψ u v x y)
    (h2 : psiV ψ u v x y / jacobian φ ψ u v x y =
      partialY ψ (u x y) (v x y) / jacobian φ ψ u v x y) :
    partialX u x y =
      partialY ψ (u x y) (v x y) / jacobian φ ψ u v x y :=
  h1.trans h2

theorem gap10 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hGeneral : differential u x y 0 1 =
      firstNumeratorU φ ψ u v x y 0 1 / jacobian φ ψ u v x y) :
    partialY u x y = -phiV φ u v x y / jacobian φ ψ u v x y := by
  simpa [differential, firstNumeratorU] using hGeneral

theorem gap11 (φ u v : ℝ → ℝ → ℝ) (I x y : ℝ) :
    -phiV φ u v x y / I =
      -partialY φ (u x y) (v x y) / I := by rfl

theorem gap12 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (h1 : partialY u x y = -phiV φ u v x y / jacobian φ ψ u v x y)
    (h2 : -phiV φ u v x y / jacobian φ ψ u v x y =
      -partialY φ (u x y) (v x y) / jacobian φ ψ u v x y) :
    partialY u x y =
      -partialY φ (u x y) (v x y) / jacobian φ ψ u v x y :=
  h1.trans h2

theorem gap13 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hGeneral : differential v x y 1 0 =
      firstNumeratorV φ ψ u v x y 1 0 / jacobian φ ψ u v x y) :
    partialX v x y = -psiU ψ u v x y / jacobian φ ψ u v x y := by
  simpa [differential, firstNumeratorV] using hGeneral

theorem gap14 (ψ u v : ℝ → ℝ → ℝ) (I x y : ℝ) :
    -psiU ψ u v x y / I =
      -partialX ψ (u x y) (v x y) / I := by rfl

theorem gap15 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (h1 : partialX v x y = -psiU ψ u v x y / jacobian φ ψ u v x y)
    (h2 : -psiU ψ u v x y / jacobian φ ψ u v x y =
      -partialX ψ (u x y) (v x y) / jacobian φ ψ u v x y) :
    partialX v x y =
      -partialX ψ (u x y) (v x y) / jacobian φ ψ u v x y :=
  h1.trans h2

theorem gap16 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hGeneral : differential v x y 0 1 =
      firstNumeratorV φ ψ u v x y 0 1 / jacobian φ ψ u v x y) :
    partialY v x y = phiU φ u v x y / jacobian φ ψ u v x y := by
  simpa [differential, firstNumeratorV] using hGeneral

theorem gap17 (φ u v : ℝ → ℝ → ℝ) (I x y : ℝ) :
    phiU φ u v x y / I =
      partialX φ (u x y) (v x y) / I := by rfl

theorem gap18 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (h1 : partialY v x y = phiU φ u v x y / jacobian φ ψ u v x y)
    (h2 : phiU φ u v x y / jacobian φ ψ u v x y =
      partialX φ (u x y) (v x y) / jacobian φ ψ u v x y) :
    partialY v x y =
      partialX φ (u x y) (v x y) / jacobian φ ψ u v x y :=
  h1.trans h2

theorem gap19 (φ ψ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hφ : 0 = quadratic φ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) +
        phiU φ u v x y * secondDifferential u x y dx dy +
        phiV φ u v x y * secondDifferential v x y dx dy)
    (hψ : 0 = quadratic ψ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) +
        psiU ψ u v x y * secondDifferential u x y dx dy +
        psiV ψ u v x y * secondDifferential v x y dx dy) :
    secondDifferential u x y dx dy =
      (phiV φ u v x y * quadratic ψ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) -
        psiV ψ u v x y * quadratic φ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy)) /
        jacobian φ ψ u v x y := by
  rw [eq_div_iff hJac]
  unfold jacobian
  linear_combination
    phiV φ u v x y * hψ - psiV ψ u v x y * hφ

theorem gap20 (φ ψ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hSecond : secondDifferential u x y dx dy =
      (phiV φ u v x y * quadratic ψ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) -
        psiV ψ u v x y * quadratic φ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy)) /
        jacobian φ ψ u v x y)
    (hDu : differential u x y dx dy =
      firstNumeratorU φ ψ u v x y dx dy / jacobian φ ψ u v x y)
    (hDv : differential v x y dx dy =
      firstNumeratorV φ ψ u v x y dx dy / jacobian φ ψ u v x y) :
    secondDifferential u x y dx dy =
      inverseSecondU φ ψ u v x y dx dy := by
  rw [hSecond]
  rw [hDu, hDv]
  unfold inverseSecondU quadratic firstNumeratorU firstNumeratorV
  field_simp [hJac]
  ring

theorem gap21 (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ) :
    secondDifferential u x y dx dy =
      partialXX u x y * dx ^ 2 +
        2 * partialXY u x y * dx * dy +
        partialYY u x y * dy ^ 2 := by rfl

theorem gap22 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hAll : ∀ dx dy : ℝ,
      secondDifferential u x y dx dy =
        inverseSecondU φ ψ u v x y dx dy) :
    partialXX u x y = inverseUxx φ ψ u v x y := by
  have h := hAll 1 0
  unfold secondDifferential inverseSecondU firstNumeratorU firstNumeratorV at h
  unfold inverseUxx
  norm_num at h
  convert h using 1 <;> ring

theorem gap23 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hAll : ∀ dx dy : ℝ,
      secondDifferential u x y dx dy =
        inverseSecondU φ ψ u v x y dx dy) :
    partialXY u x y = inverseUxy φ ψ u v x y := by
  have h10 := hAll 1 0
  have h01 := hAll 0 1
  have h11 := hAll 1 1
  unfold secondDifferential inverseSecondU
    firstNumeratorU firstNumeratorV at h10 h01 h11
  unfold inverseUxy
  norm_num at h10 h01 h11
  field_simp [hJac] at h10 h01 h11 ⊢
  ring_nf at h10 h01 h11 ⊢
  linear_combination (h11 - h10 - h01) / 2

theorem gap24 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hAll : ∀ dx dy : ℝ,
      secondDifferential u x y dx dy =
        inverseSecondU φ ψ u v x y dx dy) :
    partialYY u x y = inverseUyy φ ψ u v x y := by
  have h := hAll 0 1
  unfold secondDifferential inverseSecondU firstNumeratorU firstNumeratorV at h
  unfold inverseUyy
  norm_num at h
  convert h using 1 <;> ring

theorem gap25 (φ ψ u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hφ : 0 = quadratic φ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) +
        phiU φ u v x y * secondDifferential u x y dx dy +
        phiV φ u v x y * secondDifferential v x y dx dy)
    (hψ : 0 = quadratic ψ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) +
        psiU ψ u v x y * secondDifferential u x y dx dy +
        psiV ψ u v x y * secondDifferential v x y dx dy) :
    secondDifferential v x y dx dy =
      (psiU ψ u v x y * quadratic φ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy) -
        phiU φ u v x y * quadratic ψ (u x y) (v x y)
          (differential u x y dx dy) (differential v x y dx dy)) /
        jacobian φ ψ u v x y := by
  rw [eq_div_iff hJac]
  unfold jacobian
  linear_combination
    psiU ψ u v x y * hφ - phiU φ u v x y * hψ

end

end ProofGap.Exercise3414
