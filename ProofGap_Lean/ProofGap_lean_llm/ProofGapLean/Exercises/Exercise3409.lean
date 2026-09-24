import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3409

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

def radialForm (v dx dy : ℝ) : ℝ :=
  Real.cos v * dx + Real.sin v * dy

def angularNumerator (v dx dy : ℝ) : ℝ :=
  -Real.sin v * dx + Real.cos v * dy

def polarSecondForm (u v dx dy : ℝ) : ℝ :=
  2 / u ^ 2 *
    (Real.sin v * Real.cos v * dx ^ 2 -
      Real.cos (2 * v) * dx * dy -
      Real.sin v * Real.cos v * dy ^ 2)

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

theorem gap1 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = u p.1 p.2 * Real.cos (v p.1 p.2)) :
    dx =
      Real.cos (v x y) * differential u x y dx dy -
        u x y * Real.sin (v x y) * differential v x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hX hc
  have huLine := hasDerivAt_along_line u x y dx dy huDiff
  have hvLine := hasDerivAt_along_line v x y dx dy hvDiff
  have hleft : HasDerivAt (fun t => x + t * dx) dx 0 :=
    by
      convert (hasDerivAt_const 0 x).add
        ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp [id]
  have hright :
      HasDerivAt
        (fun t => u (x + t * dx) (y + t * dy) *
          Real.cos (v (x + t * dx) (y + t * dy)))
        (Real.cos (v x y) * differential u x y dx dy -
          u x y * Real.sin (v x y) * differential v x y dx dy) 0 := by
    convert huLine.mul hvLine.cos using 1 <;> simp [c] <;> ring
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv (fun t => x + t * dx) 0 =
        deriv (fun t => u (x + t * dx) (y + t * dy) *
          Real.cos (v (x + t * dx) (y + t * dy))) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hleft.deriv, hright.deriv] at hd'
  exact hd'

theorem gap2 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = u p.1 p.2 * Real.sin (v p.1 p.2)) :
    dy =
      Real.sin (v x y) * differential u x y dx dy +
        u x y * Real.cos (v x y) * differential v x y dx dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hY hc
  have huLine := hasDerivAt_along_line u x y dx dy huDiff
  have hvLine := hasDerivAt_along_line v x y dx dy hvDiff
  have hleft : HasDerivAt (fun t => y + t * dy) dy 0 :=
    by
      convert (hasDerivAt_const 0 y).add
        ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp [id]
  have hright :
      HasDerivAt
        (fun t => u (x + t * dx) (y + t * dy) *
          Real.sin (v (x + t * dx) (y + t * dy)))
        (Real.sin (v x y) * differential u x y dx dy +
          u x y * Real.cos (v x y) * differential v x y dx dy) 0 := by
    convert huLine.mul hvLine.sin using 1 <;> simp [c] <;> ring
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv (fun t => y + t * dy) 0 =
        deriv (fun t => u (x + t * dx) (y + t * dy) *
          Real.sin (v (x + t * dx) (y + t * dy))) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hleft.deriv, hright.deriv] at hd'
  exact hd'

theorem gap3 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hX : dx =
      Real.cos (v x y) * differential u x y dx dy -
        u x y * Real.sin (v x y) * differential v x y dx dy)
    (hY : dy =
      Real.sin (v x y) * differential u x y dx dy +
        u x y * Real.cos (v x y) * differential v x y dx dy) :
    differential u x y dx dy = radialForm (v x y) dx dy := by
  unfold radialForm
  calc
    differential u x y dx dy =
        (Real.cos (v x y) ^ 2 + Real.sin (v x y) ^ 2) *
          differential u x y dx dy := by
      rw [Real.cos_sq_add_sin_sq]
      ring
    _ = Real.cos (v x y) *
          (Real.cos (v x y) * differential u x y dx dy -
            u x y * Real.sin (v x y) * differential v x y dx dy) +
        Real.sin (v x y) *
          (Real.sin (v x y) * differential u x y dx dy +
            u x y * Real.cos (v x y) * differential v x y dx dy) := by ring
    _ = Real.cos (v x y) * dx + Real.sin (v x y) * dy := by
      rw [← hX, ← hY]

theorem gap4 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu : u x y ≠ 0)
    (hX : dx =
      Real.cos (v x y) * differential u x y dx dy -
        u x y * Real.sin (v x y) * differential v x y dx dy)
    (hY : dy =
      Real.sin (v x y) * differential u x y dx dy +
        u x y * Real.cos (v x y) * differential v x y dx dy) :
    differential v x y dx dy =
      angularNumerator (v x y) dx dy / u x y := by
  apply (eq_div_iff hu).2
  unfold angularNumerator
  calc
    differential v x y dx dy * u x y =
        u x y * differential v x y dx dy := by ring
    _ = u x y * differential v x y dx dy *
          (Real.cos (v x y) ^ 2 + Real.sin (v x y) ^ 2) := by
      rw [Real.cos_sq_add_sin_sq]
      ring
    _ =
        -Real.sin (v x y) *
            (Real.cos (v x y) * differential u x y dx dy -
              u x y * Real.sin (v x y) * differential v x y dx dy) +
          Real.cos (v x y) *
            (Real.sin (v x y) * differential u x y dx dy +
              u x y * Real.cos (v x y) * differential v x y dx dy) := by
      ring
    _ = -Real.sin (v x y) * dx + Real.cos (v x y) * dy := by
      rw [← hX, ← hY]

theorem gap5 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu : u x y ≠ 0)
    (hV : differential v x y dx dy =
      angularNumerator (v x y) dx dy / u x y) :
    u x y * differential v x y dx dy =
      angularNumerator (v x y) dx dy := by
  rw [hV]
  field_simp

theorem gap6 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huC2 : ContDiffAt ℝ 2 (Function.uncurry u) (x, y))
    (hvC2 : ContDiffAt ℝ 2 (Function.uncurry v) (x, y))
    (hAngular : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 * differential v p.1 p.2 dx dy =
        angularNumerator (v p.1 p.2) dx dy) :
    u x y * secondDifferential v x y dx dy +
        differential u x y dx dy * differential v x y dx dy =
      -Real.cos (v x y) * differential v x y dx dy * dx -
        Real.sin (v x y) * differential v x y dx dy * dy := by
  let c : ℝ → ℝ × ℝ := fun t => (x + t * dx, y + t * dy)
  have hc : Filter.Tendsto c (nhds 0) (nhds (x, y)) := by
    have hcont : ContinuousAt c 0 := by fun_prop
    have hc0 : c 0 = (x, y) := by simp [c]
    rw [← hc0]
    exact hcont
  have he := Filter.EventuallyEq.comp_tendsto hAngular hc
  have huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y) :=
    huC2.differentiableAt (by decide)
  have hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y) :=
    hvC2.differentiableAt (by decide)
  have huLine := hasDerivAt_along_line u x y dx dy huDiff
  have hvLine := hasDerivAt_along_line v x y dx dy hvDiff
  have hvDLine :=
    hasDerivAt_differential_along_line v x y dx dy hvC2
  have hleft :
      HasDerivAt
        (fun t => u (x + t * dx) (y + t * dy) *
          differential v (x + t * dx) (y + t * dy) dx dy)
        (u x y * secondDifferential v x y dx dy +
          differential u x y dx dy * differential v x y dx dy) 0 := by
    convert huLine.mul hvDLine using 1 <;> simp <;> ring
  have hright :
      HasDerivAt
        (fun t => angularNumerator
          (v (x + t * dx) (y + t * dy)) dx dy)
        (-Real.cos (v x y) * differential v x y dx dy * dx -
          Real.sin (v x y) * differential v x y dx dy * dy) 0 := by
    unfold angularNumerator
    convert (hvLine.sin.neg.mul_const dx).add
      (hvLine.cos.mul_const dy) using 1 <;> simp <;> ring
  have hd := Filter.EventuallyEq.deriv_eq he
  have hd' :
      deriv
          (fun t => u (x + t * dx) (y + t * dy) *
            differential v (x + t * dx) (y + t * dy) dx dy) 0 =
        deriv
          (fun t => angularNumerator
            (v (x + t * dx) (y + t * dy)) dx dy) 0 := by
    simpa [c, Function.comp_def] using hd
  rw [hleft.deriv, hright.deriv] at hd'
  exact hd'

theorem gap7 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hU : differential u x y dx dy = radialForm (v x y) dx dy) :
    -Real.cos (v x y) * differential v x y dx dy * dx -
        Real.sin (v x y) * differential v x y dx dy * dy =
      -differential u x y dx dy * differential v x y dx dy := by
  rw [hU]
  unfold radialForm
  ring

theorem gap8 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hSecond :
      u x y * secondDifferential v x y dx dy +
          differential u x y dx dy * differential v x y dx dy =
        -Real.cos (v x y) * differential v x y dx dy * dx -
          Real.sin (v x y) * differential v x y dx dy * dy)
    (hSimplify :
      -Real.cos (v x y) * differential v x y dx dy * dx -
          Real.sin (v x y) * differential v x y dx dy * dy =
        -differential u x y dx dy * differential v x y dx dy) :
    u x y * secondDifferential v x y dx dy +
        differential u x y dx dy * differential v x y dx dy =
      -differential u x y dx dy * differential v x y dx dy := by
  exact hSecond.trans hSimplify

theorem gap9 (z v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hvC2 : ContDiffAt ℝ 2 (Function.uncurry v) (x, y))
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = v p.1 p.2) :
    secondDifferential z x y dx dy =
      secondDifferential v x y dx dy := by
  have hzEv := hzC2.eventually (by simp)
  have hvEv := hvC2.eventually (by simp)
  have hfd :=
    Filter.EventuallyEq.fderiv (𝕜 := ℝ) hZ
  have hpx :
      (fun p : ℝ × ℝ => partialX z p.1 p.2) =ᶠ[nhds (x, y)]
        (fun p => partialX v p.1 p.2) := by
    filter_upwards [hzEv, hvEv, hfd] with p hzp hvp hp
    rw [partialX_eq_fderiv z p.1 p.2
      (hzp.differentiableAt (by decide))]
    rw [partialX_eq_fderiv v p.1 p.2
      (hvp.differentiableAt (by decide))]
    convert congrArg (fun L => L (1, 0)) hp using 1 <;>
      simp [Function.uncurry]
  have hpy :
      (fun p : ℝ × ℝ => partialY z p.1 p.2) =ᶠ[nhds (x, y)]
        (fun p => partialY v p.1 p.2) := by
    filter_upwards [hzEv, hvEv, hfd] with p hzp hvp hp
    rw [partialY_eq_fderiv z p.1 p.2
      (hzp.differentiableAt (by decide))]
    rw [partialY_eq_fderiv v p.1 p.2
      (hvp.differentiableAt (by decide))]
    convert congrArg (fun L => L (0, 1)) hp using 1 <;>
      simp [Function.uncurry]
  have hxcont : Filter.Tendsto (fun t : ℝ => (t, y))
      (nhds x) (nhds (x, y)) := by
    have h : ContinuousAt (fun t : ℝ => (t, y)) x := by fun_prop
    exact h
  have hycont : Filter.Tendsto (fun t : ℝ => (x, t))
      (nhds y) (nhds (x, y)) := by
    have h : ContinuousAt (fun t : ℝ => (x, t)) y := by fun_prop
    exact h
  have hxx := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hpx hxcont)
  have hxy := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hpx hycont)
  have hyy := Filter.EventuallyEq.deriv_eq
    (Filter.EventuallyEq.comp_tendsto hpy hycont)
  change partialXX z x y * dx ^ 2 +
      2 * partialXY z x y * dx * dy +
      partialYY z x y * dy ^ 2 =
    partialXX v x y * dx ^ 2 +
      2 * partialXY v x y * dx * dy +
      partialYY v x y * dy ^ 2
  change partialXX z x y = partialXX v x y at hxx
  change partialXY z x y = partialXY v x y at hxy
  change partialYY z x y = partialYY v x y at hyy
  rw [hxx, hxy, hyy]

theorem gap10 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu : u x y ≠ 0)
    (hSecond :
      u x y * secondDifferential v x y dx dy +
          differential u x y dx dy * differential v x y dx dy =
        -differential u x y dx dy * differential v x y dx dy) :
    secondDifferential v x y dx dy =
      -(2 / u x y) * differential u x y dx dy *
        differential v x y dx dy := by
  field_simp [hu] at *
  linarith

theorem gap11 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hZ : secondDifferential z x y dx dy =
      secondDifferential v x y dx dy)
    (hV : secondDifferential v x y dx dy =
      -(2 / u x y) * differential u x y dx dy *
        differential v x y dx dy) :
    secondDifferential z x y dx dy =
      -(2 / u x y) * differential u x y dx dy *
        differential v x y dx dy := by
  exact hZ.trans hV

theorem gap12 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu : u x y ≠ 0)
    (hZ : secondDifferential z x y dx dy =
      -(2 / u x y) * differential u x y dx dy *
        differential v x y dx dy)
    (hU : differential u x y dx dy = radialForm (v x y) dx dy)
    (hV : differential v x y dx dy =
      angularNumerator (v x y) dx dy / u x y) :
    secondDifferential z x y dx dy =
      -(2 / (u x y) ^ 2) * radialForm (v x y) dx dy *
        angularNumerator (v x y) dx dy := by
  rw [hU, hV] at hZ
  field_simp [hu] at hZ ⊢
  nlinarith

theorem gap13 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hExpanded : secondDifferential z x y dx dy =
      -(2 / (u x y) ^ 2) * radialForm (v x y) dx dy *
        angularNumerator (v x y) dx dy) :
    secondDifferential z x y dx dy =
      polarSecondForm (u x y) (v x y) dx dy := by
  rw [hExpanded]
  unfold radialForm angularNumerator polarSecondForm
  rw [Real.cos_two_mul']
  ring

theorem gap14 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : u x y ≠ 0)
    (hSecond : ∀ dx dy : ℝ,
      secondDifferential z x y dx dy =
        polarSecondForm (u x y) (v x y) dx dy) :
    partialXX z x y =
      2 * Real.sin (v x y) * Real.cos (v x y) / (u x y) ^ 2 := by
  have h := hSecond 1 0
  simp [secondDifferential, polarSecondForm] at h
  convert h using 1 <;> ring

theorem gap15 (u v : ℝ → ℝ → ℝ) (x y : ℝ) :
    2 * Real.sin (v x y) * Real.cos (v x y) / (u x y) ^ 2 =
      Real.sin (2 * v x y) / (u x y) ^ 2 := by
  rw [Real.sin_two_mul]

theorem gap16 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hXX : partialXX z x y =
      2 * Real.sin (v x y) * Real.cos (v x y) / (u x y) ^ 2)
    (hTrig : 2 * Real.sin (v x y) * Real.cos (v x y) / (u x y) ^ 2 =
      Real.sin (2 * v x y) / (u x y) ^ 2) :
    partialXX z x y =
      Real.sin (2 * v x y) / (u x y) ^ 2 := by
  exact hXX.trans hTrig

theorem gap17 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : u x y ≠ 0)
    (hSecond : ∀ dx dy : ℝ,
      secondDifferential z x y dx dy =
        polarSecondForm (u x y) (v x y) dx dy) :
    partialXY z x y =
      -Real.cos (2 * v x y) / (u x y) ^ 2 := by
  have h10 := hSecond 1 0
  have h01 := hSecond 0 1
  have h11 := hSecond 1 1
  simp [secondDifferential, polarSecondForm] at h10 h01 h11
  field_simp [hu] at h10 h01 h11 ⊢
  nlinarith

theorem gap18 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : u x y ≠ 0)
    (hSecond : ∀ dx dy : ℝ,
      secondDifferential z x y dx dy =
        polarSecondForm (u x y) (v x y) dx dy) :
    partialYY z x y =
      -Real.sin (2 * v x y) / (u x y) ^ 2 := by
  have h := hSecond 0 1
  simp [secondDifferential, polarSecondForm] at h
  rw [Real.sin_two_mul]
  field_simp [hu] at h ⊢
  nlinarith

end

end ProofGap.Exercise3409
