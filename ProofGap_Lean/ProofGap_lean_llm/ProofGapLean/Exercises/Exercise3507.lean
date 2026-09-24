import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3507

noncomputable section

open Filter

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
  partialXX f x y * dx ^ 2 + 2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def coordU (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := x + f x y

def coordV (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := y + f x y

def jacobianFactor (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  1 - partialX F u v - partialY F u v

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def pdeExpression (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXX f x y + 2 * partialXY f x y + partialYY f x y

private theorem differentiableAt_xSlice
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t => f t y) x := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    differentiableAt_id.prodMk (hasDerivAt_const x y).differentiableAt
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
    (hf (x, y)).comp x hp

private theorem differentiableAt_ySlice
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t => f x t) y := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
    (hasDerivAt_const y x).differentiableAt.prodMk differentiableAt_id
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
    (hf (x, y)).comp y hp

private theorem partialX_coordU
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    partialX (coordU f) x y = 1 + partialX f x y := by
  unfold partialX coordU
  have h := (hasDerivAt_id x).add
    (differentiableAt_xSlice hf x y).hasDerivAt
  simpa only [Pi.add_apply, id_eq] using h.deriv

private theorem partialY_coordU (f : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialY (coordU f) x y = partialY f x y := by
  unfold partialY coordU
  exact deriv_const_add x

private theorem partialX_coordV (f : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialX (coordV f) x y = partialX f x y := by
  unfold partialX coordV
  exact deriv_const_add y

private theorem partialY_coordV
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    partialY (coordV f) x y = 1 + partialY f x y := by
  unfold partialY coordV
  have h := (hasDerivAt_id y).add
    (differentiableAt_ySlice hf x y).hasDerivAt
  simpa only [Pi.add_apply, id_eq] using h.deriv

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

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) {t dg dh : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (g t, h t))
    (hg : HasDerivAt g dg t) (hh : HasDerivAt h dh t) :
    HasDerivAt (fun s => F (g s) (h s))
      (partialX F (g t) (h t) * dg +
        partialY F (g t) (h t) * dh) t := by
  let D := fderiv ℝ (Function.uncurry F) (g t, h t)
  have hc := hF.hasFDerivAt.comp t
    (hg.hasFDerivAt.prodMk hh.hasFDerivAt)
  have hc' : HasDerivAt (fun s => F (g s) (h s)) (D (dg, dh)) t := by
    simpa [D, Function.comp_def, Function.uncurry] using hc.hasDerivAt
  have hdx := partialX_eq_fderiv F (g t) (h t) hF
  have hdy := partialY_eq_fderiv F (g t) (h t) hF
  have hlin : D (dg, dh) = dg * D (1, 0) + dh * D (0, 1) := by
    calc
      D (dg, dh) = D (dg • (1, 0) + dh • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = dg • D (1, 0) + dh • D (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = dg * D (1, 0) + dh * D (0, 1) := by simp
  convert hc' using 1
  rw [hdx, hdy, hlin]
  ring

private def differentialModel (f : ℝ → ℝ → ℝ)
    (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  partialX f p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    partialY f p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem fderiv_eq_differentialModel
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) :
    fderiv ℝ (Function.uncurry f) = differentialModel f := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  rw [show v = v.1 • ((1, 0) : ℝ × ℝ) +
      v.2 • ((0, 1) : ℝ × ℝ) by ext <;> simp]
  rw [map_add, map_smul, map_smul]
  rw [← partialX_eq_fderiv f p.1 p.2 (hf p),
    ← partialY_eq_fderiv f p.1 p.2 (hf p)]
  simp [differentialModel, smul_eq_mul]
  ring

private theorem mixed_partial_comm_C2
    {f : ℝ → ℝ → ℝ} (hf : C2 f) (x y : ℝ) :
    partialX (partialY f) x y = partialXY f x y := by
  let F := Function.uncurry f
  let H := fderiv ℝ (fderiv ℝ F) (x, y)
  let ex : ℝ × ℝ := (1, 0)
  let ey : ℝ × ℝ := (0, 1)
  have hmodel :
      fderiv ℝ F = differentialModel f := by
    simpa [F] using fderiv_eq_differentialModel f hf.1
  have hmodelDiff : Differentiable ℝ (differentialModel f) := by
    exact
      (hf.2.1.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
        (hf.2.2.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hDf : Differentiable ℝ (fderiv ℝ F) := by
    rw [hmodel]
    exact hmodelDiff
  have hpartialY :
      (fun t : ℝ => partialY f t y) =ᶠ[nhds x]
        (fun t => fderiv ℝ F (t, y) ey) := by
    filter_upwards with t
    simpa [F, ey] using partialY_eq_fderiv f t y (hf.1 (t, y))
  have hpartialX :
      (fun t : ℝ => partialX f x t) =ᶠ[nhds y]
        (fun t => fderiv ℝ F (x, t) ex) := by
    filter_upwards with t
    simpa [F, ex] using partialX_eq_fderiv f x t (hf.1 (x, t))
  have hFD : HasFDerivAt (fderiv ℝ F) H (x, y) := by
    simpa [H] using (hDf (x, y)).hasFDerivAt
  let evY : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ey
  let evX : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ex
  have hEvalY := evY.hasFDerivAt.comp (x, y) hFD
  have hEvalX := evX.hasFDerivAt.comp (x, y) hFD
  have houtY :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (t, y) ey)
        (H ex ey) x := by
    have hcomp := hEvalY.comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        (hasDerivAt_const x y).hasFDerivAt)
    simpa [evY, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have houtX :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (x, t) ex)
        (H ey ex) y := by
    have hcomp := hEvalX.comp y
      ((hasDerivAt_const y x).hasFDerivAt.prodMk
        (hasDerivAt_id y).hasFDerivAt)
    simpa [evX, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have hlhs : partialX (partialY f) x y = H ex ey := by
    unfold partialX
    exact hpartialY.deriv_eq.trans houtY.deriv
  have hrhs : partialXY f x y = H ey ex := by
    unfold partialXY
    exact hpartialX.deriv_eq.trans houtX.deriv
  have hsymm : H ex ey = H ey ex :=
    second_derivative_symmetric
      (fun p => (hf.1 p).hasFDerivAt) hFD ex ey
  exact hlhs.trans (hsymm.trans hrhs.symm)

private theorem hasDerivAt_line (a da t : ℝ) :
    HasDerivAt (fun s : ℝ => a + s * da) da t := by
  convert (hasDerivAt_const t a).add ((hasDerivAt_id t).mul_const da) using 1 <;>
    ring

private theorem hasDerivAt_differential_along
    (f : ℝ → ℝ → ℝ) (hf : C2 f) (x y dx dy : ℝ)
    (hMixed : partialX (partialY f) x y = partialXY f x y) :
    HasDerivAt
      (fun t : ℝ =>
        differential f (x + t * dx) (y + t * dy) dx dy)
      (secondDifferential f x y dx dy) 0 := by
  have hX := hasDerivAt_line x dx 0
  have hY := hasDerivAt_line y dy 0
  have hpx := hasDerivAt_comp₂ (partialX f)
    (fun t : ℝ => x + t * dx) (fun t : ℝ => y + t * dy)
    (t := 0) (by simpa using hf.2.1 (x, y)) hX hY
  have hpy := hasDerivAt_comp₂ (partialY f)
    (fun t : ℝ => x + t * dx) (fun t : ℝ => y + t * dy)
    (t := 0) (by simpa using hf.2.2 (x, y)) hX hY
  have h := hpx.mul_const dx |>.add (hpy.mul_const dy)
  convert h using 1
  simp only [zero_mul, add_zero]
  change secondDifferential f x y dx dy =
    (partialXX f x y * dx + partialXY f x y * dy) * dx +
      (partialX (partialY f) x y * dx + partialYY f x y * dy) * dy
  rw [hMixed]
  unfold secondDifferential
  ring

private theorem partial_chain_x
    (f F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hF : Differentiable ℝ (Function.uncurry F))
    (hComp : ∀ a b, f a b = F (coordU f a b) (coordV f a b)) :
    partialX f x y =
      partialX F (coordU f x y) (coordV f x y) *
          partialX (coordU f) x y +
        partialY F (coordU f x y) (coordV f x y) *
          partialX (coordV f) x y := by
  let g : ℝ → ℝ := fun t => f t y
  let u : ℝ → ℝ := fun t => coordU f t y
  let v : ℝ → ℝ := fun t => coordV f t y
  have heq : g = fun t => F (u t) (v t) := by
    funext t
    exact hComp t y
  by_cases hg : DifferentiableAt ℝ g x
  · have hu : HasDerivAt u (1 + deriv g x) x := by
      simpa [u, g, coordU] using (hasDerivAt_id x).add hg.hasDerivAt
    have hv : HasDerivAt v (deriv g x) x := by
      have h := (hasDerivAt_const x y).add hg.hasDerivAt
      convert h using 1 <;> simp [v, g, coordV]
    have hc := hasDerivAt_comp₂ F u v (hF (u x, v x)) hu hv
    have hd : deriv g x =
        partialX F (u x) (v x) * (1 + deriv g x) +
          partialY F (u x) (v x) * deriv g x := by
      calc
        deriv g x = deriv (fun t => F (u t) (v t)) x :=
          congrArg (fun q : ℝ → ℝ => deriv q x) heq
        _ = _ := hc.deriv
    change deriv g x =
      partialX F (u x) (v x) * deriv u x +
        partialY F (u x) (v x) * deriv v x
    rw [hu.deriv, hv.deriv]
    exact hd
  · have hu : ¬DifferentiableAt ℝ u x := by
      intro hu
      apply hg
      have h := hu.sub differentiableAt_id
      simpa [u, g, coordU] using h
    have hv : ¬DifferentiableAt ℝ v x := by
      intro hv
      apply hg
      have h := hv.sub (hasDerivAt_const x y).differentiableAt
      simpa [v, g, coordV] using h
    simp [partialX, g, u, v, deriv_zero_of_not_differentiableAt hg,
      deriv_zero_of_not_differentiableAt hu,
      deriv_zero_of_not_differentiableAt hv]

private theorem partial_chain_y
    (f F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hF : Differentiable ℝ (Function.uncurry F))
    (hComp : ∀ a b, f a b = F (coordU f a b) (coordV f a b)) :
    partialY f x y =
      partialX F (coordU f x y) (coordV f x y) *
          partialY (coordU f) x y +
        partialY F (coordU f x y) (coordV f x y) *
          partialY (coordV f) x y := by
  let g : ℝ → ℝ := fun t => f x t
  let u : ℝ → ℝ := fun t => coordU f x t
  let v : ℝ → ℝ := fun t => coordV f x t
  have heq : g = fun t => F (u t) (v t) := by
    funext t
    exact hComp x t
  by_cases hg : DifferentiableAt ℝ g y
  · have hu : HasDerivAt u (deriv g y) y := by
      have h := (hasDerivAt_const y x).add hg.hasDerivAt
      convert h using 1 <;> simp [u, g, coordU]
    have hv : HasDerivAt v (1 + deriv g y) y := by
      simpa [v, g, coordV] using (hasDerivAt_id y).add hg.hasDerivAt
    have hc := hasDerivAt_comp₂ F u v (hF (u y, v y)) hu hv
    have hd : deriv g y =
        partialX F (u y) (v y) * deriv g y +
          partialY F (u y) (v y) * (1 + deriv g y) := by
      calc
        deriv g y = deriv (fun t => F (u t) (v t)) y :=
          congrArg (fun q : ℝ → ℝ => deriv q y) heq
        _ = _ := hc.deriv
    change deriv g y =
      partialX F (u y) (v y) * deriv u y +
        partialY F (u y) (v y) * deriv v y
    rw [hu.deriv, hv.deriv]
    exact hd
  · have hu : ¬DifferentiableAt ℝ u y := by
      intro hu
      apply hg
      have h := hu.sub (hasDerivAt_const y x).differentiableAt
      simpa [u, g, coordU] using h
    have hv : ¬DifferentiableAt ℝ v y := by
      intro hv
      apply hg
      have h := hv.sub differentiableAt_id
      simpa [v, g, coordV] using h
    simp [partialY, g, u, v, deriv_zero_of_not_differentiableAt hg,
      deriv_zero_of_not_differentiableAt hu,
      deriv_zero_of_not_differentiableAt hv]

-- Statement correction: differentiability is needed for the differential identity.
theorem gap1 (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) :
    ∀ x y dx dy,
      differential (coordU f) x y dx dy =
        dx + differential f x y dx dy := by
  intro x y dx dy
  rw [differential, differential, partialX_coordU hf, partialY_coordU]
  ring

-- Statement correction: differentiability is needed for the differential identity.
theorem gap2 (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) :
    ∀ x y dx dy,
      differential (coordV f) x y dx dy =
        dy + differential f x y dx dy := by
  intro x y dx dy
  rw [differential, differential, partialX_coordV, partialY_coordV hf]
  ring

-- Statement correction: C² regularity is needed for mixed-partial symmetry.
theorem gap3 (f : ℝ → ℝ → ℝ) (hf : C2 f) :
    ∀ x y dx dy,
      secondDifferential (coordU f) x y dx dy =
        secondDifferential (coordV f) x y dx dy := by
  intro x y dx dy
  have hxxU : partialXX (coordU f) x y = partialXX f x y := by
    unfold partialXX
    rw [show (fun t => partialX (coordU f) t y) =
        fun t => 1 + partialX f t y by
      funext t
      exact partialX_coordU hf.1 t y]
    exact deriv_const_add 1
  have hxyU : partialXY (coordU f) x y = partialXY f x y := by
    unfold partialXY
    rw [show (fun t => partialX (coordU f) x t) =
        fun t => 1 + partialX f x t by
      funext t
      exact partialX_coordU hf.1 x t]
    exact deriv_const_add 1
  have hyyU : partialYY (coordU f) x y = partialYY f x y := by
    unfold partialYY
    rw [show (fun t => partialY (coordU f) x t) =
        fun t => partialY f x t by
      funext t
      exact partialY_coordU f x t]
  have hxxV : partialXX (coordV f) x y = partialXX f x y := by
    unfold partialXX
    rw [show (fun t => partialX (coordV f) t y) =
        fun t => partialX f t y by
      funext t
      exact partialX_coordV f t y]
  have hxyV : partialXY (coordV f) x y = partialXY f x y := by
    unfold partialXY
    rw [show (fun t => partialX (coordV f) x t) =
        fun t => partialX f x t by
      funext t
      exact partialX_coordV f x t]
  have hyyV : partialYY (coordV f) x y = partialYY f x y := by
    unfold partialYY
    rw [show (fun t => partialY (coordV f) x t) =
        fun t => 1 + partialY f x t by
      funext t
      exact partialY_coordV hf.1 x t]
    exact deriv_const_add 1
  simp only [secondDifferential, hxxU, hxyU, hyyU, hxxV, hxyV, hyyV]

-- Statement correction: C² regularity is needed for the second differential formula.
theorem gap4 (f : ℝ → ℝ → ℝ) (hf : C2 f) :
    ∀ x y dx dy,
      secondDifferential (coordV f) x y dx dy =
        secondDifferential f x y dx dy := by
  intro x y dx dy
  have hxx : partialXX (coordV f) x y = partialXX f x y := by
    unfold partialXX
    rw [show (fun t => partialX (coordV f) t y) =
        fun t => partialX f t y by
      funext t
      exact partialX_coordV f t y]
  have hxy : partialXY (coordV f) x y = partialXY f x y := by
    unfold partialXY
    rw [show (fun t => partialX (coordV f) x t) =
        fun t => partialX f x t by
      funext t
      exact partialX_coordV f x t]
  have hyy : partialYY (coordV f) x y = partialYY f x y := by
    unfold partialYY
    rw [show (fun t => partialY (coordV f) x t) =
        fun t => 1 + partialY f x t by
      funext t
      exact partialY_coordV hf.1 x t]
    exact deriv_const_add 1
  simp only [secondDifferential, hxx, hxy, hyy]

theorem gap5 (f F : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hF : C2 F)
    (hComp : ∀ a b, f a b = F (coordU f a b) (coordV f a b)) :
    differential f x y dx dy =
      partialX F (coordU f x y) (coordV f x y) *
          differential (coordU f) x y dx dy +
        partialY F (coordU f x y) (coordV f x y) *
          differential (coordV f) x y dx dy := by
  have hx := partial_chain_x f F x y hF.1 hComp
  have hy := partial_chain_y f F x y hF.1 hComp
  unfold differential
  rw [hx, hy]
  ring

-- Statement correction: differentiability is needed to expand the coordinate differentials.
theorem gap6 (f F : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) (x y dx dy : ℝ) :
    partialX F (coordU f x y) (coordV f x y) *
          differential (coordU f) x y dx dy +
        partialY F (coordU f x y) (coordV f x y) *
          differential (coordV f) x y dx dy =
      (partialX F (coordU f x y) (coordV f x y) +
          partialY F (coordU f x y) (coordV f x y)) *
          differential f x y dx dy +
        partialX F (coordU f x y) (coordV f x y) * dx +
        partialY F (coordU f x y) (coordV f x y) * dy := by
  rw [gap1 f hf x y dx dy, gap2 f hf x y dx dy]
  ring

-- Statement correction: differentiability is needed to expand the coordinate differentials.
theorem gap7 (f F : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f)) (x y dx dy : ℝ)
    (hChain :
      differential f x y dx dy =
        partialX F (coordU f x y) (coordV f x y) *
            differential (coordU f) x y dx dy +
          partialY F (coordU f x y) (coordV f x y) *
            differential (coordV f) x y dx dy) :
    differential f x y dx dy =
      (partialX F (coordU f x y) (coordV f x y) +
          partialY F (coordU f x y) (coordV f x y)) *
          differential f x y dx dy +
        partialX F (coordU f x y) (coordV f x y) * dx +
        partialY F (coordU f x y) (coordV f x y) * dy := by
  exact hChain.trans (gap6 f F hf x y dx dy)

theorem gap8 (f F : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hA : jacobianFactor F (coordU f x y) (coordV f x y) ≠ 0)
    (hExpanded :
      differential f x y dx dy =
        (partialX F (coordU f x y) (coordV f x y) +
            partialY F (coordU f x y) (coordV f x y)) *
            differential f x y dx dy +
          partialX F (coordU f x y) (coordV f x y) * dx +
          partialY F (coordU f x y) (coordV f x y) * dy) :
    differential f x y dx dy =
      1 / jacobianFactor F (coordU f x y) (coordV f x y) *
          partialX F (coordU f x y) (coordV f x y) * dx +
        1 / jacobianFactor F (coordU f x y) (coordV f x y) *
          partialY F (coordU f x y) (coordV f x y) * dy := by
  unfold jacobianFactor at hA ⊢
  field_simp [hA]
  ring_nf at hExpanded ⊢
  linarith

theorem gap9 (f F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hA : jacobianFactor F (coordU f x y) (coordV f x y) ≠ 0)
    (hDifferential : ∀ dx dy,
      differential f x y dx dy =
        1 / jacobianFactor F (coordU f x y) (coordV f x y) *
            partialX F (coordU f x y) (coordV f x y) * dx +
          1 / jacobianFactor F (coordU f x y) (coordV f x y) *
            partialY F (coordU f x y) (coordV f x y) * dy) :
    partialX f x y =
      1 / jacobianFactor F (coordU f x y) (coordV f x y) *
        partialX F (coordU f x y) (coordV f x y) := by
  simpa [differential] using hDifferential 1 0

theorem gap10 (f F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hA : jacobianFactor F (coordU f x y) (coordV f x y) ≠ 0)
    (hDifferential : ∀ dx dy,
      differential f x y dx dy =
        1 / jacobianFactor F (coordU f x y) (coordV f x y) *
            partialX F (coordU f x y) (coordV f x y) * dx +
          1 / jacobianFactor F (coordU f x y) (coordV f x y) *
            partialY F (coordU f x y) (coordV f x y) * dy) :
    partialY f x y =
      1 / jacobianFactor F (coordU f x y) (coordV f x y) *
        partialY F (coordU f x y) (coordV f x y) := by
  simpa [differential] using hDifferential 0 1

-- Statement correction: the Jacobian factor must be nonzero before division.
theorem gap11 (f F : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hA : jacobianFactor F (coordU f x y) (coordV f x y) ≠ 0)
    (hDu : differential (coordU f) x y dx dy =
      dx + differential f x y dx dy)
    (hDz : differential f x y dx dy =
      1 / jacobianFactor F (coordU f x y) (coordV f x y) *
          partialX F (coordU f x y) (coordV f x y) * dx +
        1 / jacobianFactor F (coordU f x y) (coordV f x y) *
          partialY F (coordU f x y) (coordV f x y) * dy) :
    differential (coordU f) x y dx dy =
      (1 - partialY F (coordU f x y) (coordV f x y)) /
          jacobianFactor F (coordU f x y) (coordV f x y) * dx +
        partialY F (coordU f x y) (coordV f x y) /
          jacobianFactor F (coordU f x y) (coordV f x y) * dy := by
  rw [hDu, hDz]
  unfold jacobianFactor at hA ⊢
  field_simp [hA]
  ring

-- Statement correction: the Jacobian factor must be nonzero before division.
theorem gap12 (f F : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hA : jacobianFactor F (coordU f x y) (coordV f x y) ≠ 0)
    (hDv : differential (coordV f) x y dx dy =
      dy + differential f x y dx dy)
    (hDz : differential f x y dx dy =
      1 / jacobianFactor F (coordU f x y) (coordV f x y) *
          partialX F (coordU f x y) (coordV f x y) * dx +
        1 / jacobianFactor F (coordU f x y) (coordV f x y) *
          partialY F (coordU f x y) (coordV f x y) * dy) :
    differential (coordV f) x y dx dy =
      partialX F (coordU f x y) (coordV f x y) /
          jacobianFactor F (coordU f x y) (coordV f x y) * dx +
        (1 - partialX F (coordU f x y) (coordV f x y)) /
          jacobianFactor F (coordU f x y) (coordV f x y) * dy := by
  rw [hDv, hDz]
  unfold jacobianFactor at hA ⊢
  field_simp [hA]
  ring

theorem gap13 (f F : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : C2 f)
    (hF : C2 F)
    (hComp : ∀ a b, f a b = F (coordU f a b) (coordV f a b)) :
    secondDifferential f x y dx dy =
      partialXX F (coordU f x y) (coordV f x y) *
          differential (coordU f) x y dx dy ^ 2 +
        2 * partialXY F (coordU f x y) (coordV f x y) *
          differential (coordU f) x y dx dy *
          differential (coordV f) x y dx dy +
        partialYY F (coordU f x y) (coordV f x y) *
          differential (coordV f) x y dx dy ^ 2 +
        partialX F (coordU f x y) (coordV f x y) *
          secondDifferential (coordU f) x y dx dy +
        partialY F (coordU f x y) (coordV f x y) *
          secondDifferential (coordV f) x y dx dy := by
  let X : ℝ → ℝ := fun t => x + t * dx
  let Y : ℝ → ℝ := fun t => y + t * dy
  let Z : ℝ → ℝ := fun t => f (X t) (Y t)
  let U : ℝ → ℝ := fun t => coordU f (X t) (Y t)
  let V : ℝ → ℝ := fun t => coordV f (X t) (Y t)
  let H : ℝ → ℝ := fun t => F (U t) (V t)
  let UP : ℝ → ℝ := fun t =>
    dx + differential f (X t) (Y t) dx dy
  let VP : ℝ → ℝ := fun t =>
    dy + differential f (X t) (Y t) dx dy
  let z2 : ℝ := secondDifferential f x y dx dy
  let du : ℝ := differential (coordU f) x y dx dy
  let dv : ℝ := differential (coordV f) x y dx dy
  have hMixedF := mixed_partial_comm_C2 hf x y
  have hMixedOuter :=
    mixed_partial_comm_C2 hF (coordU f x y) (coordV f x y)
  have hX (t : ℝ) : HasDerivAt X dx t := by
    simpa [X] using hasDerivAt_line x dx t
  have hY (t : ℝ) : HasDerivAt Y dy t := by
    simpa [Y] using hasDerivAt_line y dy t
  have hZ (t : ℝ) :
      HasDerivAt Z (differential f (X t) (Y t) dx dy) t := by
    simpa [Z, differential] using
      hasDerivAt_comp₂ f X Y (hf.1 (X t, Y t)) (hX t) (hY t)
  have hZprime :
      (fun t => deriv Z t) =
        fun t => differential f (X t) (Y t) dx dy := by
    funext t
    exact (hZ t).deriv
  have hz2model :
      HasDerivAt
        (fun t => differential f (X t) (Y t) dx dy) z2 0 := by
    simpa [X, Y, z2] using
      hasDerivAt_differential_along f hf x y dx dy hMixedF
  have hZsecond : HasDerivAt (fun t => deriv Z t) z2 0 := by
    rw [hZprime]
    exact hz2model
  have hU (t : ℝ) : HasDerivAt U (UP t) t := by
    simpa [U, UP, Z, coordU] using (hX t).add (hZ t)
  have hV (t : ℝ) : HasDerivAt V (VP t) t := by
    simpa [V, VP, Z, coordV] using (hY t).add (hZ t)
  have hUPsecond : HasDerivAt UP z2 0 := by
    simpa only [UP, Pi.add_apply, zero_add] using
      (hasDerivAt_const 0 dx).add hz2model
  have hVPsecond : HasDerivAt VP z2 0 := by
    simpa only [VP, Pi.add_apply, zero_add] using
      (hasDerivAt_const 0 dy).add hz2model
  have hUP0 : UP 0 = du := by
    rw [show du = dx + differential f x y dx dy by
      exact gap1 f hf.1 x y dx dy]
    simp [UP, X, Y]
  have hVP0 : VP 0 = dv := by
    rw [show dv = dy + differential f x y dx dy by
      exact gap2 f hf.1 x y dx dy]
    simp [VP, X, Y]
  have hU0 : HasDerivAt U du 0 := by
    rw [← hUP0]
    exact hU 0
  have hV0 : HasDerivAt V dv 0 := by
    rw [← hVP0]
    exact hV 0
  have hH (t : ℝ) :
      HasDerivAt H
        (partialX F (U t) (V t) * UP t +
          partialY F (U t) (V t) * VP t) t := by
    simpa [H] using
      hasDerivAt_comp₂ F U V (hF.1 (U t, V t)) (hU t) (hV t)
  have hHprime :
      (fun t => deriv H t) =
        fun t =>
          partialX F (U t) (V t) * UP t +
            partialY F (U t) (V t) * VP t := by
    funext t
    exact (hH t).deriv
  have hA := hasDerivAt_comp₂ (partialX F) U V
    (t := 0) (by
      simpa [U, V, X, Y] using
        hF.2.1 (coordU f x y, coordV f x y))
    hU0 hV0
  have hB := hasDerivAt_comp₂ (partialY F) U V
    (t := 0) (by
      simpa [U, V, X, Y] using
        hF.2.2 (coordU f x y, coordV f x y))
    hU0 hV0
  have hHmodelRaw := (hA.mul hUPsecond).add (hB.mul hVPsecond)
  have hHsecondModel :
      HasDerivAt (fun t => deriv H t)
        (partialXX F (coordU f x y) (coordV f x y) * du ^ 2 +
          2 * partialXY F (coordU f x y) (coordV f x y) * du * dv +
          partialYY F (coordU f x y) (coordV f x y) * dv ^ 2 +
          (partialX F (coordU f x y) (coordV f x y) +
            partialY F (coordU f x y) (coordV f x y)) * z2) 0 := by
    rw [hHprime]
    convert hHmodelRaw using 1
    rw [hUP0, hVP0]
    simp only [U, V, X, Y, zero_mul, add_zero]
    change
      partialXX F (coordU f x y) (coordV f x y) * du ^ 2 +
            2 * partialXY F (coordU f x y) (coordV f x y) * du * dv +
          partialYY F (coordU f x y) (coordV f x y) * dv ^ 2 +
        (partialX F (coordU f x y) (coordV f x y) +
            partialY F (coordU f x y) (coordV f x y)) * z2 =
      ((partialXX F (coordU f x y) (coordV f x y) * du +
            partialXY F (coordU f x y) (coordV f x y) * dv) * du +
          partialX F (coordU f x y) (coordV f x y) * z2) +
        ((partialX (partialY F) (coordU f x y) (coordV f x y) * du +
            partialYY F (coordU f x y) (coordV f x y) * dv) * dv +
          partialY F (coordU f x y) (coordV f x y) * z2)
    rw [hMixedOuter]
    ring
  have hHeq : H = Z := by
    funext t
    exact hComp (X t) (Y t) |>.symm
  have hHprimeRelation : (fun t => deriv H t) = fun t => deriv Z t := by
    funext t
    rw [hHeq]
  have hHsecondRelation :
      HasDerivAt (fun t => deriv H t) z2 0 := by
    rw [hHprimeRelation]
    exact hZsecond
  have hkey := hHsecondModel.unique hHsecondRelation
  have hU2 :
      secondDifferential (coordU f) x y dx dy = z2 := by
    exact (gap3 f hf x y dx dy).trans (gap4 f hf x y dx dy)
  have hV2 :
      secondDifferential (coordV f) x y dx dy = z2 :=
    gap4 f hf x y dx dy
  rw [hU2, hV2]
  dsimp [du, dv, z2] at hkey ⊢
  ring_nf at hkey ⊢
  linarith

theorem gap14 (f : ℝ → ℝ → ℝ)
    (hPDE : ∀ x y, pdeExpression f x y = 0) :
    ∀ x y, partialXX f x y + 2 * partialXY f x y + partialYY f x y = 0 := by
  intro x y
  exact hPDE x y

theorem gap15 (f F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : C2 f)
    (hF : C2 F)
    (hComp : ∀ a b, f a b = F (coordU f a b) (coordV f a b))
    (hA : jacobianFactor F (coordU f x y) (coordV f x y) ≠ 0)
    (hPDE : pdeExpression f x y = 0) :
    partialXX F (coordU f x y) (coordV f x y) +
        2 * partialXY F (coordU f x y) (coordV f x y) +
        partialYY F (coordU f x y) (coordV f x y) = 0 := by
  have hChain := gap5 f F x y 1 1 hF hComp
  have hExpanded := gap7 f F hf.1 x y 1 1 hChain
  have hDz := gap8 f F x y 1 1 hA hExpanded
  have hDuRaw := gap1 f hf.1 x y 1 1
  have hDvRaw := gap2 f hf.1 x y 1 1
  have hDuFormula := gap11 f F x y 1 1 hA hDuRaw hDz
  have hDvFormula := gap12 f F x y 1 1 hA hDvRaw hDz
  have hDu :
      differential (coordU f) x y 1 1 =
        1 / jacobianFactor F (coordU f x y) (coordV f x y) := by
    rw [hDuFormula]
    field_simp [hA]
    ring
  have hDv :
      differential (coordV f) x y 1 1 =
        1 / jacobianFactor F (coordU f x y) (coordV f x y) := by
    rw [hDvFormula]
    field_simp [hA]
    ring
  have hSecond := gap13 f F x y 1 1 hf hF hComp
  have hSf : secondDifferential f x y 1 1 = 0 := by
    simpa [secondDifferential, pdeExpression] using hPDE
  have hU2 :
      secondDifferential (coordU f) x y 1 1 =
        secondDifferential f x y 1 1 :=
    (gap3 f hf x y 1 1).trans (gap4 f hf x y 1 1)
  have hV2 :
      secondDifferential (coordV f) x y 1 1 =
        secondDifferential f x y 1 1 :=
    gap4 f hf x y 1 1
  rw [hSf, hDu, hDv, hU2, hV2, hSf] at hSecond
  field_simp [hA] at hSecond
  ring_nf at hSecond ⊢
  exact hSecond.symm

theorem gap16 (f F : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : C2 f)
    (hF : C2 F)
    (hComp : ∀ a b, f a b = F (coordU f a b) (coordV f a b))
    (hA : jacobianFactor F (coordU f x y) (coordV f x y) ≠ 0) :
    pdeExpression f x y = 0 →
      pdeExpression F (coordU f x y) (coordV f x y) = 0 := by
  intro hPDE
  exact gap15 f F x y hf hF hComp hA hPDE

end

end ProofGap.Exercise3507
