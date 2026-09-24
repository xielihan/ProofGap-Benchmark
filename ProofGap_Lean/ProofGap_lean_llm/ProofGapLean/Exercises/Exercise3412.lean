import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3412

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def implicitDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  (Real.exp x * (1 + x) * dx + Real.exp y * (1 + y) * dy) /
    (Real.exp (z x y) * (1 + z x y))

def quotientDifferential (z : ℝ → ℝ → ℝ)
    (x y dx dy dz : ℝ) : ℝ :=
  ((y + z x y) * dx - (x + z x y) * dy + (y - x) * dz) /
    (y + z x y) ^ 2

theorem gap1 (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 * Real.exp (z p.1 p.2) =
        p.1 * Real.exp p.1 + p.2 * Real.exp p.2) :
    Real.exp (z x y) * (1 + z x y) *
        differential z x y dx dy =
      Real.exp x * (1 + x) * dx +
        Real.exp y * (1 + y) * dy := by
  have hPairXDiff : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    exact differentiableAt_id.prodMk (differentiableAt_const y)
  have hPairYDiff : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    exact (differentiableAt_const x).prodMk differentiableAt_id
  have hzXDiff : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      hzDiff.comp x hPairXDiff
  have hzYDiff : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      hzDiff.comp y hPairYDiff
  have hzX : HasDerivAt (fun t : ℝ => z t y) (partialX z x y) x := by
    simpa [partialX] using hzXDiff.hasDerivAt
  have hzY : HasDerivAt (fun t : ℝ => z x t) (partialY z x y) y := by
    simpa [partialY] using hzYDiff.hasDerivAt
  have hExpZX : HasDerivAt (fun t : ℝ => Real.exp (z t y))
      (Real.exp (z x y) * partialX z x y) x := by
    convert ((Real.hasDerivAt_exp (z x y)).comp x hzX) using 1 <;> ring
  have hExpZY : HasDerivAt (fun t : ℝ => Real.exp (z x t))
      (Real.exp (z x y) * partialY z x y) y := by
    convert ((Real.hasDerivAt_exp (z x y)).comp y hzY) using 1 <;> ring
  have hLeftX : HasDerivAt
      (fun t : ℝ => z t y * Real.exp (z t y))
      (Real.exp (z x y) * (1 + z x y) * partialX z x y) x := by
    convert (hzX.mul hExpZX) using 1 <;> ring
  have hLeftY : HasDerivAt
      (fun t : ℝ => z x t * Real.exp (z x t))
      (Real.exp (z x y) * (1 + z x y) * partialY z x y) y := by
    convert (hzY.mul hExpZY) using 1 <;> ring
  have hRightX : HasDerivAt
      (fun t : ℝ => t * Real.exp t + y * Real.exp y)
      (Real.exp x * (1 + x)) x := by
    convert
      (((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)).add
        (hasDerivAt_const (x := x) (c := y * Real.exp y))) using 1 <;>
      simp [id_eq] <;> ring
  have hRightY : HasDerivAt
      (fun t : ℝ => x * Real.exp x + t * Real.exp t)
      (Real.exp y * (1 + y)) y := by
    convert
      ((hasDerivAt_const (x := y) (c := x * Real.exp x)).add
        ((hasDerivAt_id y).mul (Real.hasDerivAt_exp y))) using 1 <;>
      simp [id_eq] <;> ring
  have hPairXCont : ContinuousAt (fun t : ℝ => (t, y)) x := by
    exact continuousAt_id.prodMk continuousAt_const
  have hPairYCont : ContinuousAt (fun t : ℝ => (x, t)) y := by
    exact continuousAt_const.prodMk continuousAt_id
  have hEqX :
      (fun t : ℝ => z t y * Real.exp (z t y)) =ᶠ[nhds x]
        (fun t : ℝ => t * Real.exp t + y * Real.exp y) := by
    simpa using hPairXCont.eventually hImplicit
  have hEqY :
      (fun t : ℝ => z x t * Real.exp (z x t)) =ᶠ[nhds y]
        (fun t : ℝ => x * Real.exp x + t * Real.exp t) := by
    simpa using hPairYCont.eventually hImplicit
  have hx : Real.exp (z x y) * (1 + z x y) * partialX z x y =
      Real.exp x * (1 + x) := by
    calc
      Real.exp (z x y) * (1 + z x y) * partialX z x y =
          deriv (fun t : ℝ => z t y * Real.exp (z t y)) x := hLeftX.deriv.symm
      _ = deriv (fun t : ℝ => t * Real.exp t + y * Real.exp y) x :=
        hEqX.deriv_eq
      _ = Real.exp x * (1 + x) := hRightX.deriv
  have hy : Real.exp (z x y) * (1 + z x y) * partialY z x y =
      Real.exp y * (1 + y) := by
    calc
      Real.exp (z x y) * (1 + z x y) * partialY z x y =
          deriv (fun t : ℝ => z x t * Real.exp (z x t)) y := hLeftY.deriv.symm
      _ = deriv (fun t : ℝ => x * Real.exp x + t * Real.exp t) y :=
        hEqY.deriv_eq
      _ = Real.exp y * (1 + y) := hRightY.deriv
  simp only [differential]
  calc
    Real.exp (z x y) * (1 + z x y) *
          (partialX z x y * dx + partialY z x y * dy) =
        (Real.exp (z x y) * (1 + z x y) * partialX z x y) * dx +
          (Real.exp (z x y) * (1 + z x y) * partialY z x y) * dy := by
            ring
    _ = Real.exp x * (1 + x) * dx + Real.exp y * (1 + y) * dy := by
      rw [hx, hy]

theorem gap2 (u z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hDen : y + z x y ≠ 0)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = (p.1 + z p.1 p.2) / (p.2 + z p.1 p.2)) :
    differential u x y dx dy =
      ((y + z x y) * dx + (y + z x y) * differential z x y dx dy -
        (x + z x y) * dy - (x + z x y) * differential z x y dx dy) /
        (y + z x y) ^ 2 := by
  have hPairXDiff : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    exact differentiableAt_id.prodMk (differentiableAt_const y)
  have hPairYDiff : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by
    exact (differentiableAt_const x).prodMk differentiableAt_id
  have hzXDiff : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    simpa [Function.comp_def, Function.uncurry] using
      hzDiff.comp x hPairXDiff
  have hzYDiff : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    simpa [Function.comp_def, Function.uncurry] using
      hzDiff.comp y hPairYDiff
  have hzX : HasDerivAt (fun t : ℝ => z t y) (partialX z x y) x := by
    simpa [partialX] using hzXDiff.hasDerivAt
  have hzY : HasDerivAt (fun t : ℝ => z x t) (partialY z x y) y := by
    simpa [partialY] using hzYDiff.hasDerivAt
  have hNumX : HasDerivAt (fun t : ℝ => t + z t y)
      (1 + partialX z x y) x := by
    simpa using (hasDerivAt_id x).add hzX
  have hDenX : HasDerivAt (fun t : ℝ => y + z t y)
      (partialX z x y) x := by
    convert ((hasDerivAt_const (x := x) (c := y)).add hzX) using 1 <;> simp
  have hNumY : HasDerivAt (fun t : ℝ => x + z x t)
      (partialY z x y) y := by
    convert ((hasDerivAt_const (x := y) (c := x)).add hzY) using 1 <;> simp
  have hDenY : HasDerivAt (fun t : ℝ => t + z x t)
      (1 + partialY z x y) y := by
    simpa using (hasDerivAt_id y).add hzY
  have hQuotX : HasDerivAt
      (fun t : ℝ => (t + z t y) / (y + z t y))
      (((1 + partialX z x y) * (y + z x y) -
          (x + z x y) * partialX z x y) / (y + z x y) ^ 2) x := by
    convert (hNumX.div hDenX hDen) using 1 <;> ring
  have hQuotY : HasDerivAt
      (fun t : ℝ => (x + z x t) / (t + z x t))
      ((partialY z x y * (y + z x y) -
          (x + z x y) * (1 + partialY z x y)) / (y + z x y) ^ 2) y := by
    convert (hNumY.div hDenY hDen) using 1 <;> ring
  have hPairXCont : ContinuousAt (fun t : ℝ => (t, y)) x := by
    exact continuousAt_id.prodMk continuousAt_const
  have hPairYCont : ContinuousAt (fun t : ℝ => (x, t)) y := by
    exact continuousAt_const.prodMk continuousAt_id
  have hEqX :
      (fun t : ℝ => u t y) =ᶠ[nhds x]
        (fun t : ℝ => (t + z t y) / (y + z t y)) := by
    simpa using hPairXCont.eventually hU
  have hEqY :
      (fun t : ℝ => u x t) =ᶠ[nhds y]
        (fun t : ℝ => (x + z x t) / (t + z x t)) := by
    simpa using hPairYCont.eventually hU
  have hUX : partialX u x y =
      ((1 + partialX z x y) * (y + z x y) -
        (x + z x y) * partialX z x y) / (y + z x y) ^ 2 := by
    calc
      partialX u x y = deriv (fun t : ℝ => u t y) x := by rfl
      _ = deriv (fun t : ℝ => (t + z t y) / (y + z t y)) x :=
        hEqX.deriv_eq
      _ = ((1 + partialX z x y) * (y + z x y) -
          (x + z x y) * partialX z x y) / (y + z x y) ^ 2 :=
        hQuotX.deriv
  have hUY : partialY u x y =
      (partialY z x y * (y + z x y) -
        (x + z x y) * (1 + partialY z x y)) / (y + z x y) ^ 2 := by
    calc
      partialY u x y = deriv (fun t : ℝ => u x t) y := by rfl
      _ = deriv (fun t : ℝ => (x + z x t) / (t + z x t)) y :=
        hEqY.deriv_eq
      _ = (partialY z x y * (y + z x y) -
          (x + z x y) * (1 + partialY z x y)) / (y + z x y) ^ 2 :=
        hQuotY.deriv
  simp only [differential]
  rw [hUX, hUY]
  ring

theorem gap3 (u z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hDen : y + z x y ≠ 0)
    (hExpanded : differential u x y dx dy =
      ((y + z x y) * dx + (y + z x y) * differential z x y dx dy -
        (x + z x y) * dy - (x + z x y) * differential z x y dx dy) /
        (y + z x y) ^ 2) :
    differential u x y dx dy =
      quotientDifferential z x y dx dy (differential z x y dx dy) := by
  rw [hExpanded]
  unfold quotientDifferential
  ring

theorem gap4 (u z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hQuotientDen : y + z x y ≠ 0)
    (hImplicitDen : Real.exp (z x y) * (1 + z x y) ≠ 0)
    (hQuotient : differential u x y dx dy =
      quotientDifferential z x y dx dy (differential z x y dx dy))
    (hZ : Real.exp (z x y) * (1 + z x y) *
        differential z x y dx dy =
      Real.exp x * (1 + x) * dx +
        Real.exp y * (1 + y) * dy) :
    differential u x y dx dy =
      ((y + z x y) * dx - (x + z x y) * dy +
        ((y - x) * Real.exp x * (1 + x) /
          (Real.exp (z x y) * (1 + z x y))) * dx +
        ((y - x) * Real.exp y * (1 + y) /
          (Real.exp (z x y) * (1 + z x y))) * dy) /
        (y + z x y) ^ 2 := by
  have hD : differential z x y dx dy =
      (Real.exp x * (1 + x) * dx + Real.exp y * (1 + y) * dy) /
        (Real.exp (z x y) * (1 + z x y)) := by
    apply (eq_div_iff hImplicitDen).2
    simpa only [mul_comm] using hZ
  rw [hQuotient]
  unfold quotientDifferential
  rw [hD]
  ring

theorem gap5 (u z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hYZ : y + z x y ≠ 0)
    (hZOne : z x y + 1 ≠ 0)
    (hDirectional : differential u x y 1 0 =
      ((y + z x y) +
        (y - x) * Real.exp x * (1 + x) /
          (Real.exp (z x y) * (1 + z x y))) /
        (y + z x y) ^ 2) :
    partialX u x y =
      1 / (y + z x y) +
        ((x + 1) * (y - x) /
          ((z x y + 1) * (y + z x y) ^ 2)) *
          Real.exp (x - z x y) := by
  simp only [differential, mul_one, mul_zero, add_zero, zero_add] at hDirectional
  have hOneZ : 1 + z x y ≠ 0 := by
    simpa [add_comm] using hZOne
  rw [hDirectional, Real.exp_sub]
  field_simp [hYZ, hZOne, hOneZ, Real.exp_ne_zero] <;> ring

theorem gap6 (u z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hYZ : y + z x y ≠ 0)
    (hZOne : z x y + 1 ≠ 0)
    (hDirectional : differential u x y 0 1 =
      (-(x + z x y) +
        (y - x) * Real.exp y * (1 + y) /
          (Real.exp (z x y) * (1 + z x y))) /
        (y + z x y) ^ 2) :
    partialY u x y =
      -(x + z x y) / (y + z x y) ^ 2 +
        ((y + 1) * (y - x) /
          ((z x y + 1) * (y + z x y) ^ 2)) *
          Real.exp (y - z x y) := by
  simp only [differential, mul_one, mul_zero, add_zero, zero_add] at hDirectional
  have hOneZ : 1 + z x y ≠ 0 := by
    simpa [add_comm] using hZOne
  rw [hDirectional, Real.exp_sub]
  field_simp [hYZ, hZOne, hOneZ, Real.exp_ne_zero] <;> ring

end

end ProofGap.Exercise3412
