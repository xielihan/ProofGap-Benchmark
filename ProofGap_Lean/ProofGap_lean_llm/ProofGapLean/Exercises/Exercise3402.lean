import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise3402

noncomputable section

def secondDeriv (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t

private theorem deriv_differentiableAt_of_c2 {f : ℝ → ℝ} {t : ℝ}
    (hf : ContDiffAt ℝ 2 f t) :
    DifferentiableAt ℝ (deriv f) t := by
  have hfderiv :
      ContDiffAt ℝ (2 - 1) (fderiv ℝ f) t :=
    hf.fderiv_right (by decide)
  have hone :
      ContDiffAt ℝ (2 - 1) (fun _ : ℝ => (1 : ℝ)) t :=
    contDiffAt_const
  have happly :
      ContDiffAt ℝ (2 - 1)
        (fun s : ℝ => (fderiv ℝ f s) (1 : ℝ)) t :=
    hfderiv.clm_apply hone
  simpa only [deriv] using happly.differentiableAt (by decide)

theorem gap1 (x y : ℝ → ℝ) (t : ℝ)
    (hxDiff : DifferentiableAt ℝ x t)
    (hyDiff : DifferentiableAt ℝ y t)
    (hQuadratic :
      ∀ᶠ s in nhds t,
        (x s) ^ 2 + (y s) ^ 2 = (1 / 2 : ℝ) * s ^ 2) :
    2 * x t * deriv x t + 2 * y t * deriv y t = t := by
  have hLeft :
      HasDerivAt (fun s : ℝ => (x s) ^ 2 + (y s) ^ 2)
        (2 * x t * deriv x t + 2 * y t * deriv y t) t := by
    convert (hxDiff.hasDerivAt.pow 2).add (hyDiff.hasDerivAt.pow 2) using 1 <;>
      norm_num <;> ring
  have hRight :
      HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * s ^ 2) t t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ) using 1 <;>
      norm_num <;> ring
  calc
    2 * x t * deriv x t + 2 * y t * deriv y t =
        deriv (fun s : ℝ => (x s) ^ 2 + (y s) ^ 2) t := hLeft.deriv.symm
    _ = deriv (fun s : ℝ => (1 / 2 : ℝ) * s ^ 2) t :=
      Filter.EventuallyEq.deriv_eq hQuadratic
    _ = t := hRight.deriv

theorem gap2 (x y : ℝ → ℝ) (t : ℝ)
    (hxDiff : DifferentiableAt ℝ x t)
    (hyDiff : DifferentiableAt ℝ y t)
    (hLinear :
      ∀ᶠ s in nhds t, x s + y s + s = 2) :
    deriv x t + deriv y t + 1 = 0 := by
  have hLeft :
      HasDerivAt (fun s : ℝ => x s + y s + s)
        (deriv x t + deriv y t + 1) t := by
    simpa using
      (hxDiff.hasDerivAt.add hyDiff.hasDerivAt).add (hasDerivAt_id t)
  have hRight : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 t :=
    hasDerivAt_const t 2
  have hEq :
      (fun s : ℝ => x s + y s + s) =ᶠ[nhds t]
        (fun _ : ℝ => (2 : ℝ)) := hLinear
  have hRight' :
      HasDerivAt (fun s : ℝ => x s + y s + s) 0 t :=
    hRight.congr_of_eventuallyEq hEq
  exact hLeft.unique hRight'

theorem gap3 (x y : ℝ → ℝ) (t : ℝ)
    (hxC2 : ContDiffAt ℝ 2 x t)
    (hyC2 : ContDiffAt ℝ 2 y t)
    (hQuadratic :
      ∀ᶠ s in nhds t,
        (x s) ^ 2 + (y s) ^ 2 = (1 / 2 : ℝ) * s ^ 2) :
    2 * (deriv x t) ^ 2 + 2 * x t * secondDeriv x t +
        2 * (deriv y t) ^ 2 + 2 * y t * secondDeriv y t = 1 := by
  have hFirst :
      ∀ᶠ s in nhds t,
        2 * x s * deriv x s + 2 * y s * deriv y s = s := by
    filter_upwards [hxC2.eventually (by decide),
      hyC2.eventually (by decide),
      eventually_eventually_nhds.2 hQuadratic] with s hxs hys hs
    exact gap1 x y s
      (hxs.differentiableAt (by decide))
      (hys.differentiableAt (by decide)) hs
  have hxDiff : DifferentiableAt ℝ x t :=
    hxC2.differentiableAt (by decide)
  have hyDiff : DifferentiableAt ℝ y t :=
    hyC2.differentiableAt (by decide)
  have hxDerivDiff : DifferentiableAt ℝ (deriv x) t :=
    deriv_differentiableAt_of_c2 hxC2
  have hyDerivDiff : DifferentiableAt ℝ (deriv y) t :=
    deriv_differentiableAt_of_c2 hyC2
  have hLeft :
      HasDerivAt
        (fun s : ℝ => 2 * x s * deriv x s + 2 * y s * deriv y s)
        (2 * (deriv x t) ^ 2 + 2 * x t * secondDeriv x t +
          2 * (deriv y t) ^ 2 + 2 * y t * secondDeriv y t) t := by
    convert
      ((hxDiff.hasDerivAt.const_mul 2).mul hxDerivDiff.hasDerivAt).add
        ((hyDiff.hasDerivAt.const_mul 2).mul hyDerivDiff.hasDerivAt)
      using 1 <;> simp [secondDeriv] <;> ring
  have hRight : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hEq :
      (fun s : ℝ => 2 * x s * deriv x s + 2 * y s * deriv y s) =ᶠ[nhds t]
        (fun s : ℝ => s) := hFirst
  have hRight' :
      HasDerivAt
        (fun s : ℝ => 2 * x s * deriv x s + 2 * y s * deriv y s) 1 t :=
    hRight.congr_of_eventuallyEq hEq
  exact hLeft.unique hRight'

theorem gap4 (x y : ℝ → ℝ) (t : ℝ)
    (hxC2 : ContDiffAt ℝ 2 x t)
    (hyC2 : ContDiffAt ℝ 2 y t)
    (hLinear :
      ∀ᶠ s in nhds t, x s + y s + s = 2) :
    secondDeriv x t + secondDeriv y t = 0 := by
  have hFirst :
      ∀ᶠ s in nhds t, deriv x s + deriv y s + 1 = 0 := by
    filter_upwards [hxC2.eventually (by decide),
      hyC2.eventually (by decide),
      eventually_eventually_nhds.2 hLinear] with s hxs hys hs
    exact gap2 x y s
      (hxs.differentiableAt (by decide))
      (hys.differentiableAt (by decide)) hs
  have hxDerivDiff : DifferentiableAt ℝ (deriv x) t :=
    deriv_differentiableAt_of_c2 hxC2
  have hyDerivDiff : DifferentiableAt ℝ (deriv y) t :=
    deriv_differentiableAt_of_c2 hyC2
  have hLeft :
      HasDerivAt (fun s : ℝ => deriv x s + deriv y s + 1)
        (secondDeriv x t + secondDeriv y t) t := by
    simpa [secondDeriv] using
      (hxDerivDiff.hasDerivAt.add hyDerivDiff.hasDerivAt).add_const (1 : ℝ)
  have hRight : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t :=
    hasDerivAt_const t 0
  have hEq :
      (fun s : ℝ => deriv x s + deriv y s + 1) =ᶠ[nhds t]
        (fun _ : ℝ => (0 : ℝ)) := hFirst
  have hRight' :
      HasDerivAt (fun s : ℝ => deriv x s + deriv y s + 1) 0 t :=
    hRight.congr_of_eventuallyEq hEq
  exact hLeft.unique hRight'

theorem gap5 (x y : ℝ → ℝ)
    (hxValue : x 2 = 1) (hyValue : y 2 = -1)
    (hQuadraticDerivative :
      2 * x 2 * deriv x 2 + 2 * y 2 * deriv y 2 = 2)
    (hLinearDerivative : deriv x 2 + deriv y 2 + 1 = 0) :
    deriv x 2 = 0 := by
  rw [hxValue, hyValue] at hQuadraticDerivative
  linarith

theorem gap6 (x y : ℝ → ℝ)
    (hxValue : x 2 = 1) (hyValue : y 2 = -1)
    (hQuadraticDerivative :
      2 * x 2 * deriv x 2 + 2 * y 2 * deriv y 2 = 2)
    (hLinearDerivative : deriv x 2 + deriv y 2 + 1 = 0)
    (hxDerivative : deriv x 2 = 0) :
    deriv y 2 = -1 := by
  linarith

theorem gap7 (x y : ℝ → ℝ)
    (hSecondLinear : secondDeriv x 2 + secondDeriv y 2 = 0) :
    secondDeriv x 2 = -secondDeriv y 2 := by
  linarith

theorem gap8 (x y : ℝ → ℝ)
    (hxValue : x 2 = 1) (hyValue : y 2 = -1)
    (hxDerivative : deriv x 2 = 0)
    (hyDerivative : deriv y 2 = -1)
    (hSecondQuadratic :
      2 * (deriv x 2) ^ 2 + 2 * x 2 * secondDeriv x 2 +
          2 * (deriv y 2) ^ 2 + 2 * y 2 * secondDeriv y 2 = 1)
    (hOpposite : secondDeriv x 2 = -secondDeriv y 2) :
    secondDeriv x 2 = -(1 / 4 : ℝ) := by
  norm_num [hxValue, hyValue, hxDerivative, hyDerivative] at hSecondQuadratic
  linarith

theorem gap9 (x y : ℝ → ℝ)
    (hOpposite : secondDeriv x 2 = -secondDeriv y 2)
    (hxSecond : secondDeriv x 2 = -(1 / 4 : ℝ)) :
    secondDeriv y 2 = (1 / 4 : ℝ) := by
  linarith

end

end ProofGap.Exercise3402
