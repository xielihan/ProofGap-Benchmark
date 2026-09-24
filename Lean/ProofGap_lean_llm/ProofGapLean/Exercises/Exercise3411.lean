import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3411

noncomputable section

def firstDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def secondDerivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

private theorem hasDerivAt_curve (y : ℝ → ℝ) (x : ℝ)
    (hy : DifferentiableAt ℝ y x) :
    HasDerivAt (fun t => t ^ 2 - t * y t + (y t) ^ 2)
      (2 * x - y x - x * firstDerivative y x +
        2 * y x * firstDerivative y x) x := by
  unfold firstDerivative
  convert ((hasDerivAt_id x).pow 2).sub
      ((hasDerivAt_id x).mul hy.hasDerivAt) |>.add
        (hy.hasDerivAt.pow 2) using 1 <;> simp [id] <;> ring

private theorem hasDerivAt_first_curve_expression (y : ℝ → ℝ) (x : ℝ)
    (hy : DifferentiableAt ℝ y x)
    (hyd : DifferentiableAt ℝ (deriv y) x) :
    HasDerivAt
      (fun t => 2 * t - y t - t * deriv y t + 2 * y t * deriv y t)
      (2 - 2 * firstDerivative y x - x * secondDerivative y x +
        2 * (firstDerivative y x) ^ 2 +
        2 * y x * secondDerivative y x) x := by
  unfold firstDerivative secondDerivative
  convert (((hasDerivAt_id x).const_mul 2).sub hy.hasDerivAt).sub
      ((hasDerivAt_id x).mul hyd.hasDerivAt) |>.add
        ((hy.hasDerivAt.mul hyd.hasDerivAt).const_mul 2) using 1
  · funext t
    simp [id]
    ring
  · simp [id]
    ring

theorem gap1 (y : ℝ → ℝ) (x : ℝ)
    (hyDiff : DifferentiableAt ℝ y x)
    (hCurve : ∀ᶠ t in nhds x, t ^ 2 - t * y t + (y t) ^ 2 = 1) :
    2 * x - y x - x * firstDerivative y x +
      2 * y x * firstDerivative y x = 0 := by
  have h := Filter.EventuallyEq.deriv_eq hCurve
  rw [(hasDerivAt_curve y x hyDiff).deriv, deriv_const] at h
  exact h

theorem gap2 (y : ℝ → ℝ) (x : ℝ)
    (hyC2 : ContDiffAt ℝ 2 y x)
    (hCurve : ∀ᶠ t in nhds x, t ^ 2 - t * y t + (y t) ^ 2 = 1) :
    2 - 2 * firstDerivative y x - x * secondDerivative y x +
        2 * (firstDerivative y x) ^ 2 +
        2 * y x * secondDerivative y x = 0 := by
  have hyEv := hyC2.eventually (by simp)
  have hcurveDeriv :
      deriv (fun t => t ^ 2 - t * y t + (y t) ^ 2) =ᶠ[nhds x]
        (fun t => 2 * t - y t - t * deriv y t + 2 * y t * deriv y t) := by
    filter_upwards [hyEv] with t ht
    exact (hasDerivAt_curve y t (ht.differentiableAt (by decide))).deriv
  have hzero :
      (fun t => 2 * t - y t - t * deriv y t + 2 * y t * deriv y t) =ᶠ[nhds x]
        (fun _ => 0) := by
    exact hcurveDeriv.symm.trans <| (Filter.EventuallyEq.deriv hCurve).trans <| by
      simp
  have hydiff : DifferentiableAt ℝ (deriv y) x :=
    (hyC2.derivWithin (m := 1) (by norm_num)).differentiableAt (by decide)
  have h := hzero.deriv_eq
  rw [(hasDerivAt_first_curve_expression y x
    (hyC2.differentiableAt (by decide)) hydiff).deriv, deriv_const] at h
  exact h

theorem gap3 (y : ℝ → ℝ) (x : ℝ)
    (hDen : x - 2 * y x ≠ 0)
    (hFirst : 2 * x - y x - x * firstDerivative y x +
      2 * y x * firstDerivative y x = 0) :
    firstDerivative y x = (2 * x - y x) / (x - 2 * y x) := by
  field_simp [hDen]
  linarith

theorem gap4 (y : ℝ → ℝ) (x : ℝ)
    (hDen : x - 2 * y x ≠ 0)
    (hFirst : firstDerivative y x =
      (2 * x - y x) / (x - 2 * y x))
    (hSecond : 2 - 2 * firstDerivative y x - x * secondDerivative y x +
        2 * (firstDerivative y x) ^ 2 +
        2 * y x * secondDerivative y x = 0) :
    secondDerivative y x =
      6 * (x ^ 2 - x * y x + (y x) ^ 2) /
        (x - 2 * y x) ^ 3 := by
  rw [hFirst] at hSecond
  field_simp [hDen] at hSecond ⊢
  nlinarith

theorem gap5 (y : ℝ → ℝ) (x : ℝ)
    (hCurve : x ^ 2 - x * y x + (y x) ^ 2 = 1) :
    6 * (x ^ 2 - x * y x + (y x) ^ 2) /
        (x - 2 * y x) ^ 3 =
      6 / (x - 2 * y x) ^ 3 := by
  simp [hCurve]

theorem gap6 (y : ℝ → ℝ) (x : ℝ)
    (hGeneral : secondDerivative y x =
      6 * (x ^ 2 - x * y x + (y x) ^ 2) /
        (x - 2 * y x) ^ 3)
    (hCurve : 6 * (x ^ 2 - x * y x + (y x) ^ 2) /
        (x - 2 * y x) ^ 3 =
      6 / (x - 2 * y x) ^ 3) :
    secondDerivative y x = 6 / (x - 2 * y x) ^ 3 := by
  exact hGeneral.trans hCurve

theorem gap7 (y z : ℝ → ℝ) (x : ℝ)
    (hyDiff : DifferentiableAt ℝ y x)
    (hzDiff : DifferentiableAt ℝ z x)
    (hZ : ∀ᶠ t in nhds x, z t = t ^ 2 + (y t) ^ 2) :
    firstDerivative z x =
      2 * x + 2 * y x * firstDerivative y x := by
  have h := Filter.EventuallyEq.deriv_eq hZ
  have hg :
      HasDerivAt (fun t => t ^ 2 + (y t) ^ 2)
        (2 * x + 2 * y x * firstDerivative y x) x := by
    unfold firstDerivative
    convert ((hasDerivAt_id x).pow 2).add (hyDiff.hasDerivAt.pow 2) using 1 <;>
      simp [id] <;> ring
  rw [hzDiff.hasDerivAt.deriv, hg.deriv] at h
  exact h

theorem gap8 (y : ℝ → ℝ) (x : ℝ)
    (hFirst : firstDerivative y x =
      (2 * x - y x) / (x - 2 * y x)) :
    2 * x + 2 * y x * firstDerivative y x =
      2 * x + 2 * y x * ((2 * x - y x) / (x - 2 * y x)) := by
  rw [hFirst]

theorem gap9 (y : ℝ → ℝ) (x : ℝ)
    (hDen : x - 2 * y x ≠ 0) :
    2 * x + 2 * y x * ((2 * x - y x) / (x - 2 * y x)) =
      2 * (x ^ 2 - (y x) ^ 2) / (x - 2 * y x) := by
  field_simp [hDen]
  ring

theorem gap10 (y z : ℝ → ℝ) (x : ℝ)
    (hZ : firstDerivative z x =
      2 * x + 2 * y x * firstDerivative y x)
    (hSub : 2 * x + 2 * y x * firstDerivative y x =
      2 * (x ^ 2 - (y x) ^ 2) / (x - 2 * y x)) :
    firstDerivative z x =
      2 * (x ^ 2 - (y x) ^ 2) / (x - 2 * y x) := by
  exact hZ.trans hSub

theorem gap11 (y z : ℝ → ℝ) (x : ℝ)
    (hyC2 : ContDiffAt ℝ 2 y x)
    (hzC2 : ContDiffAt ℝ 2 z x)
    (hZ : ∀ᶠ t in nhds x, z t = t ^ 2 + (y t) ^ 2) :
    secondDerivative z x =
      2 + 2 * (firstDerivative y x) ^ 2 +
        2 * secondDerivative y x * y x := by
  have hyEv := hyC2.eventually (by simp)
  have hderiv :
      deriv (fun t => t ^ 2 + (y t) ^ 2) =ᶠ[nhds x]
        (fun t => 2 * t + 2 * y t * deriv y t) := by
    filter_upwards [hyEv] with t ht
    have h :
        HasDerivAt (fun s => s ^ 2 + (y s) ^ 2)
          (2 * t + 2 * y t * deriv y t) t := by
      convert ((hasDerivAt_id t).pow 2).add
        ((ht.differentiableAt (by decide)).hasDerivAt.pow 2) using 1 <;>
        simp [id] <;> ring
    exact h.deriv
  have hsecond :=
    Filter.EventuallyEq.deriv_eq (Filter.EventuallyEq.deriv hZ)
  rw [show deriv (deriv z) x = secondDerivative z x by rfl] at hsecond
  rw [hderiv.deriv_eq] at hsecond
  have hydiff : DifferentiableAt ℝ (deriv y) x :=
    (hyC2.derivWithin (m := 1) (by norm_num)).differentiableAt (by decide)
  have hformula :
      HasDerivAt (fun t => 2 * t + 2 * y t * deriv y t)
        (2 + 2 * (firstDerivative y x) ^ 2 +
          2 * secondDerivative y x * y x) x := by
    unfold firstDerivative secondDerivative
    convert ((hasDerivAt_id x).const_mul 2).add
      ((hyC2.differentiableAt (by decide)).hasDerivAt.mul hydiff.hasDerivAt
        |>.const_mul 2) using 1
    · funext t
      simp [id]
      ring
    · simp [id]
      ring
  rw [hformula.deriv] at hsecond
  exact hsecond

theorem gap12 (y : ℝ → ℝ) (x : ℝ)
    (hImplicitSecond :
      2 - 2 * firstDerivative y x - x * secondDerivative y x +
          2 * (firstDerivative y x) ^ 2 +
          2 * y x * secondDerivative y x = 0) :
    2 + 2 * (firstDerivative y x) ^ 2 +
        2 * secondDerivative y x * y x =
      2 * firstDerivative y x + x * secondDerivative y x := by
  linarith

theorem gap13 (y : ℝ → ℝ) (x : ℝ)
    (hFirst : firstDerivative y x =
      (2 * x - y x) / (x - 2 * y x))
    (hSecond : secondDerivative y x =
      6 / (x - 2 * y x) ^ 3) :
    2 * firstDerivative y x + x * secondDerivative y x =
      2 * (2 * x - y x) / (x - 2 * y x) +
        6 * x / (x - 2 * y x) ^ 3 := by
  rw [hFirst, hSecond]
  ring

theorem gap14 (y z : ℝ → ℝ) (x : ℝ)
    (hZ : secondDerivative z x =
      2 + 2 * (firstDerivative y x) ^ 2 +
        2 * secondDerivative y x * y x)
    (hImplicit : 2 + 2 * (firstDerivative y x) ^ 2 +
        2 * secondDerivative y x * y x =
      2 * firstDerivative y x + x * secondDerivative y x)
    (hSub : 2 * firstDerivative y x + x * secondDerivative y x =
      2 * (2 * x - y x) / (x - 2 * y x) +
        6 * x / (x - 2 * y x) ^ 3) :
    secondDerivative z x =
      2 * (2 * x - y x) / (x - 2 * y x) +
        6 * x / (x - 2 * y x) ^ 3 := by
  exact hZ.trans (hImplicit.trans hSub)

end

end ProofGap.Exercise3411
