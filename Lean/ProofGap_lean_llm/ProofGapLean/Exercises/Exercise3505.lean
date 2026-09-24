import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3505

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

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def coordX (x y : ℝ) : ℝ := x + y

def coordY (x y : ℝ) : ℝ := y / (x + y)

def physicalExpression (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * partialXX f x y + y * partialXY f x y + partialX f x y

def transformedExpression (f : ℝ → ℝ → ℝ) (X Y : ℝ) : ℝ :=
  X * partialXX f X Y - Y * partialXY f X Y + partialX f X Y

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
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) {x dg dh : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (g x, h x))
    (hg : HasDerivAt g dg x) (hh : HasDerivAt h dh x) :
    HasDerivAt (fun t => F (g t) (h t))
      (partialX F (g x) (h x) * dg +
        partialY F (g x) (h x) * dh) x := by
  let D := fderiv ℝ (Function.uncurry F) (g x, h x)
  have hc := hF.hasFDerivAt.comp x
    (hg.hasFDerivAt.prodMk hh.hasFDerivAt)
  have hc' : HasDerivAt (fun t => F (g t) (h t)) (D (dg, dh)) x := by
    simpa [D, Function.comp_def, Function.uncurry] using hc.hasDerivAt
  have hdx := partialX_eq_fderiv F (g x) (h x) hF
  have hdy := partialY_eq_fderiv F (g x) (h x) hF
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

private theorem hasDerivAt_coordY_x (x y : ℝ) (hxy : x + y ≠ 0) :
    HasDerivAt (fun t => coordY t y) (-y / (x + y) ^ 2) x := by
  have hden : HasDerivAt (fun t : ℝ => t + y) 1 x := by
    simpa using (hasDerivAt_id x).add_const y
  have hquot :=
    (hasDerivAt_const x y).div hden hxy
  convert hquot using 1
  simp

private theorem hasDerivAt_coordY_y (x y : ℝ) (hxy : x + y ≠ 0) :
    HasDerivAt (fun t => coordY x t) (x / (x + y) ^ 2) y := by
  have hden : HasDerivAt (fun t : ℝ => x + t) 1 y := by
    simpa using (hasDerivAt_const y x).add (hasDerivAt_id y)
  have hquot := (hasDerivAt_id y).div hden hxy
  convert hquot using 1
  simp [id]

theorem gap1 :
    ∀ x y : ℝ, coordX x y = x + y := by
  intro x y
  rfl

theorem gap2 :
    ∀ x y : ℝ, x + y ≠ 0 →
      coordY x y = y / coordX x y := by
  intro x y _
  rfl

theorem gap3 :
    ∀ x y : ℝ, x + y ≠ 0 →
      y / coordX x y = y / (x + y) := by
  intro x y _
  rfl

theorem gap4 :
    ∀ x y : ℝ, x + y ≠ 0 →
      y / (x + y) = 1 - x / (x + y) := by
  intro x y hxy
  field_simp [hxy]
  ring

theorem gap5 :
    ∀ x y : ℝ, x + y ≠ 0 →
      coordY x y = 1 - x / (x + y) := by
  intro x y hxy
  exact (gap2 x y hxy).trans ((gap3 x y hxy).trans (gap4 x y hxy))

theorem gap6 :
    ∀ x y : ℝ, partialX coordX x y = 1 := by
  intro x y
  unfold partialX coordX
  simpa using ((hasDerivAt_id x).add_const y).deriv

theorem gap7 :
    ∀ x y : ℝ, partialY coordX x y = 1 := by
  intro x y
  change deriv (fun t : ℝ => x + t) y = 1
  convert ((hasDerivAt_const y x).add (hasDerivAt_id y)).deriv using 1 <;>
    ring

theorem gap8 :
    ∀ x y : ℝ, x + y ≠ 0 →
      partialX coordY x y = -y / (x + y) ^ 2 := by
  intro x y hxy
  exact (hasDerivAt_coordY_x x y hxy).deriv

theorem gap9 :
    ∀ x y : ℝ, x + y ≠ 0 →
      partialY coordY x y = x / (x + y) ^ 2 := by
  intro x y hxy
  exact (hasDerivAt_coordY_y x y hxy).deriv

theorem gap10 (f F : ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x y, x + y ≠ 0 →
      f x y = F (coordX x y) (coordY x y)) :
    ∀ x y, x + y ≠ 0 →
      partialX f x y =
        partialX F (coordX x y) (coordY x y) -
          y / (x + y) ^ 2 * partialY F (coordX x y) (coordY x y) := by
  intro x y hxy
  have hne : ∀ᶠ t in nhds x, t + y ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne hxy
  have heq :
      (fun t => f t y) =ᶠ[nhds x]
        (fun t => F (coordX t y) (coordY t y)) := by
    filter_upwards [hne] with t ht
    exact hComp t y ht
  have hX : HasDerivAt (fun t => coordX t y) 1 x := by
    simpa [coordX] using (hasDerivAt_id x).add_const y
  have hY := hasDerivAt_coordY_x x y hxy
  have hchain := hasDerivAt_comp₂ F
    (fun t => coordX t y) (fun t => coordY t y)
    (hF.1 (coordX x y, coordY x y)) hX hY
  change deriv (fun t => f t y) x =
    partialX F (coordX x y) (coordY x y) -
      y / (x + y) ^ 2 * partialY F (coordX x y) (coordY x y)
  rw [heq.deriv_eq, hchain.deriv]
  ring

theorem gap11 (f F : ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x y, x + y ≠ 0 →
      f x y = F (coordX x y) (coordY x y)) :
    ∀ x y, x + y ≠ 0 →
      partialXX f x y =
        partialXX F (coordX x y) (coordY x y) -
          (2 * y) / (x + y) ^ 2 *
            partialXY F (coordX x y) (coordY x y) +
          y ^ 2 / (x + y) ^ 4 *
            partialYY F (coordX x y) (coordY x y) +
          (2 * y) / (x + y) ^ 3 *
            partialY F (coordX x y) (coordY x y) := by
  intro x y hxy
  let U : ℝ → ℝ := fun t => coordX t y
  let V : ℝ → ℝ := fun t => coordY t y
  let c : ℝ → ℝ := fun t => -y / (t + y) ^ 2
  have hne : ∀ᶠ t in nhds x, t + y ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne hxy
  have heq :
      (fun t => partialX f t y) =ᶠ[nhds x]
        (fun t => partialX F (U t) (V t) +
          c t * partialY F (U t) (V t)) := by
    filter_upwards [hne] with t ht
    have h := gap10 f F hF hComp t y ht
    dsimp [U, V, c]
    convert h using 1 <;> ring
  have hU : HasDerivAt U 1 x := by
    simpa [U, coordX] using (hasDerivAt_id x).add_const y
  have hV : HasDerivAt V (-y / (x + y) ^ 2) x := by
    simpa [V] using hasDerivAt_coordY_x x y hxy
  have hden : HasDerivAt (fun t : ℝ => t + y) 1 x := by
    simpa using (hasDerivAt_id x).add_const y
  have hsq :
      HasDerivAt (fun t : ℝ => (t + y) ^ 2) (2 * (x + y)) x := by
    convert hden.pow 2 using 1 <;> norm_num <;> ring
  have hc0 := (hasDerivAt_const x (-y)).div hsq (pow_ne_zero 2 hxy)
  have hc : HasDerivAt c (2 * y / (x + y) ^ 3) x := by
    convert hc0 using 1
    field_simp [hxy]
    ring
  have hA := hasDerivAt_comp₂ (partialX F) U V
    (hF.2.1 (U x, V x)) hU hV
  have hB := hasDerivAt_comp₂ (partialY F) U V
    (hF.2.2 (U x, V x)) hU hV
  have hmodel := hA.add (hc.mul hB)
  have hmodelDeriv :
      deriv (fun t => partialX F (U t) (V t) +
        c t * partialY F (U t) (V t)) x =
        partialX (partialX F) (U x) (V x) * 1 +
            partialY (partialX F) (U x) (V x) *
              (-y / (x + y) ^ 2) +
          (2 * y / (x + y) ^ 3 * partialY F (U x) (V x) +
            c x * (partialX (partialY F) (U x) (V x) * 1 +
              partialY (partialY F) (U x) (V x) *
                (-y / (x + y) ^ 2))) := by
    simpa only [Pi.add_apply, Pi.mul_apply] using hmodel.deriv
  change deriv (fun t => partialX f t y) x =
    partialXX F (coordX x y) (coordY x y) -
      (2 * y) / (x + y) ^ 2 *
        partialXY F (coordX x y) (coordY x y) +
      y ^ 2 / (x + y) ^ 4 *
        partialYY F (coordX x y) (coordY x y) +
      (2 * y) / (x + y) ^ 3 *
        partialY F (coordX x y) (coordY x y)
  rw [heq.deriv_eq, hmodelDeriv]
  rw [mixed_partial_comm_C2 hF (U x) (V x)]
  dsimp [U, V, c]
  change
    partialXX F (coordX x y) (coordY x y) * 1 +
        partialXY F (coordX x y) (coordY x y) *
          (-y / (x + y) ^ 2) +
      (2 * y / (x + y) ^ 3 *
          partialY F (coordX x y) (coordY x y) +
        (-y / (x + y) ^ 2) *
          (partialXY F (coordX x y) (coordY x y) * 1 +
            partialYY F (coordX x y) (coordY x y) *
              (-y / (x + y) ^ 2))) =
    partialXX F (coordX x y) (coordY x y) -
      (2 * y) / (x + y) ^ 2 *
        partialXY F (coordX x y) (coordY x y) +
      y ^ 2 / (x + y) ^ 4 *
        partialYY F (coordX x y) (coordY x y) +
      (2 * y) / (x + y) ^ 3 *
        partialY F (coordX x y) (coordY x y)
  field_simp [hxy]
  ring

theorem gap12 (f F : ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x y, x + y ≠ 0 →
      f x y = F (coordX x y) (coordY x y)) :
    ∀ x y, x + y ≠ 0 →
      partialXY f x y =
        partialXX F (coordX x y) (coordY x y) +
          (x - y) / (x + y) ^ 2 *
            partialXY F (coordX x y) (coordY x y) -
          (x * y) / (x + y) ^ 4 *
            partialYY F (coordX x y) (coordY x y) -
          (x - y) / (x + y) ^ 3 *
            partialY F (coordX x y) (coordY x y) := by
  intro x y hxy
  let U : ℝ → ℝ := fun t => coordX x t
  let V : ℝ → ℝ := fun t => coordY x t
  let c : ℝ → ℝ := fun t => -t / (x + t) ^ 2
  have hne : ∀ᶠ t in nhds y, x + t ≠ 0 :=
    (continuousAt_const.add continuousAt_id).eventually_ne hxy
  have heq :
      (fun t => partialX f x t) =ᶠ[nhds y]
        (fun t => partialX F (U t) (V t) +
          c t * partialY F (U t) (V t)) := by
    filter_upwards [hne] with t ht
    have h := gap10 f F hF hComp x t ht
    dsimp [U, V, c]
    convert h using 1 <;> ring
  have hU : HasDerivAt U 1 y := by
    simpa [U, coordX] using
      (hasDerivAt_const y x).add (hasDerivAt_id y)
  have hV : HasDerivAt V (x / (x + y) ^ 2) y := by
    simpa [V] using hasDerivAt_coordY_y x y hxy
  have hden : HasDerivAt (fun t : ℝ => x + t) 1 y := by
    simpa using (hasDerivAt_const y x).add (hasDerivAt_id y)
  have hsq :
      HasDerivAt (fun t : ℝ => (x + t) ^ 2) (2 * (x + y)) y := by
    convert hden.pow 2 using 1 <;> norm_num <;> ring
  have hc0 := (hasDerivAt_id y).neg.div hsq (pow_ne_zero 2 hxy)
  have hc : HasDerivAt c (-(x - y) / (x + y) ^ 3) y := by
    convert hc0 using 1
    simp [id]
    field_simp [hxy]
    ring
  have hA := hasDerivAt_comp₂ (partialX F) U V
    (hF.2.1 (U y, V y)) hU hV
  have hB := hasDerivAt_comp₂ (partialY F) U V
    (hF.2.2 (U y, V y)) hU hV
  have hmodel := hA.add (hc.mul hB)
  have hmodelDeriv :
      deriv (fun t => partialX F (U t) (V t) +
        c t * partialY F (U t) (V t)) y =
        partialX (partialX F) (U y) (V y) * 1 +
            partialY (partialX F) (U y) (V y) *
              (x / (x + y) ^ 2) +
          (-(x - y) / (x + y) ^ 3 *
              partialY F (U y) (V y) +
            c y * (partialX (partialY F) (U y) (V y) * 1 +
              partialY (partialY F) (U y) (V y) *
                (x / (x + y) ^ 2))) := by
    simpa only [Pi.add_apply, Pi.mul_apply] using hmodel.deriv
  change deriv (fun t => partialX f x t) y =
    partialXX F (coordX x y) (coordY x y) +
      (x - y) / (x + y) ^ 2 *
        partialXY F (coordX x y) (coordY x y) -
      (x * y) / (x + y) ^ 4 *
        partialYY F (coordX x y) (coordY x y) -
      (x - y) / (x + y) ^ 3 *
        partialY F (coordX x y) (coordY x y)
  rw [heq.deriv_eq, hmodelDeriv]
  rw [mixed_partial_comm_C2 hF (U y) (V y)]
  dsimp [U, V, c]
  change
    partialXX F (coordX x y) (coordY x y) * 1 +
        partialXY F (coordX x y) (coordY x y) *
          (x / (x + y) ^ 2) +
      (-(x - y) / (x + y) ^ 3 *
          partialY F (coordX x y) (coordY x y) +
        (-y / (x + y) ^ 2) *
          (partialXY F (coordX x y) (coordY x y) * 1 +
            partialYY F (coordX x y) (coordY x y) *
              (x / (x + y) ^ 2))) =
    partialXX F (coordX x y) (coordY x y) +
      (x - y) / (x + y) ^ 2 *
        partialXY F (coordX x y) (coordY x y) -
      (x * y) / (x + y) ^ 4 *
        partialYY F (coordX x y) (coordY x y) -
      (x - y) / (x + y) ^ 3 *
        partialY F (coordX x y) (coordY x y)
  field_simp [hxy]
  ring

theorem gap13 (A f : ℝ → ℝ → ℝ)
    (hA : ∀ x y, A x y = physicalExpression f x y) :
    ∀ x y, A x y =
      x * partialXX f x y + y * partialXY f x y + partialX f x y := by
  intro x y
  simpa [physicalExpression] using hA x y

theorem gap14 (f F : ℝ → ℝ → ℝ)
    (hF : C2 F)
    (hComp : ∀ x y, x + y ≠ 0 →
      f x y = F (coordX x y) (coordY x y)) :
    ∀ x y, x + y ≠ 0 →
      physicalExpression f x y =
        transformedExpression F (coordX x y) (coordY x y) := by
  intro x y hxy
  rw [physicalExpression, transformedExpression, gap10 f F hF hComp x y hxy,
    gap11 f F hF hComp x y hxy, gap12 f F hF hComp x y hxy]
  simp only [coordX, coordY]
  field_simp [hxy]
  ring

theorem gap15 (A f F : ℝ → ℝ → ℝ)
    (hA : ∀ x y, A x y = physicalExpression f x y)
    (hTransform : ∀ x y, x + y ≠ 0 →
      physicalExpression f x y =
        transformedExpression F (coordX x y) (coordY x y)) :
    ∀ x y, x + y ≠ 0 →
      A x y = transformedExpression F (coordX x y) (coordY x y) := by
  intro x y hxy
  exact (hA x y).trans (hTransform x y hxy)

end

end ProofGap.Exercise3505
