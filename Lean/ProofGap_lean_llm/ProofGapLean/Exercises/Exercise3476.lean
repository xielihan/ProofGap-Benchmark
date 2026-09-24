import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3476

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (u v du dv : ℝ) : ℝ :=
  partialX f u v * du + partialY f u v * dv

def solveDenominator (x y w : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  1 + x u v * partialY w u v + y u v * partialX w u v

theorem gap1 (x y z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (u, v))
    (hwDiff : DifferentiableAt ℝ (Function.uncurry w) (u, v))
    (hW : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      w p.1 p.2 = x p.1 p.2 * y p.1 p.2 - z p.1 p.2) :
    differential w u v du dv =
      y u v * differential x u v du dv +
        x u v * differential y u v du dv -
        differential z u v du dv := by
  have hconstV : DifferentiableAt ℝ (fun _ : ℝ => v) u :=
    differentiableAt_const (c := v)
  have hconstU : DifferentiableAt ℝ (fun _ : ℝ => u) v :=
    differentiableAt_const (c := u)
  have hcoordX : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u :=
    ((hasFDerivAt_id u).prodMk (hasFDerivAt_const v u)).differentiableAt
  have hcoordY : DifferentiableAt ℝ (fun t : ℝ => (u, t)) v :=
    ((hasFDerivAt_const u v).prodMk (hasFDerivAt_id v)).differentiableAt
  have hxX : DifferentiableAt ℝ (fun t : ℝ => x t v) u := by
    simpa [Function.uncurry] using hxDiff.comp u hcoordX
  have hyX : DifferentiableAt ℝ (fun t : ℝ => y t v) u := by
    simpa [Function.uncurry] using hyDiff.comp u hcoordX
  have hzX : DifferentiableAt ℝ (fun t : ℝ => z t v) u := by
    simpa [Function.uncurry] using hzDiff.comp u hcoordX
  have hxY : DifferentiableAt ℝ (fun t : ℝ => x u t) v := by
    simpa [Function.uncurry] using hxDiff.comp v hcoordY
  have hyY : DifferentiableAt ℝ (fun t : ℝ => y u t) v := by
    simpa [Function.uncurry] using hyDiff.comp v hcoordY
  have hzY : DifferentiableAt ℝ (fun t : ℝ => z u t) v := by
    simpa [Function.uncurry] using hzDiff.comp v hcoordY
  have hW_X :
      (fun t : ℝ => w t v) =ᶠ[nhds u]
        (fun t : ℝ => x t v * y t v - z t v) := by
    simpa using hcoordX.continuousAt.eventually hW
  have hW_Y :
      (fun t : ℝ => w u t) =ᶠ[nhds v]
        (fun t : ℝ => x u t * y u t - z u t) := by
    simpa using hcoordY.continuousAt.eventually hW
  have hDerivX :
      HasDerivAt (fun t : ℝ => x t v * y t v - z t v)
        (deriv (fun t : ℝ => x t v) u * y u v +
          x u v * deriv (fun t : ℝ => y t v) u -
          deriv (fun t : ℝ => z t v) u) u :=
    (hxX.hasDerivAt.mul hyX.hasDerivAt).sub hzX.hasDerivAt
  have hDerivY :
      HasDerivAt (fun t : ℝ => x u t * y u t - z u t)
        (deriv (fun t : ℝ => x u t) v * y u v +
          x u v * deriv (fun t : ℝ => y u t) v -
          deriv (fun t : ℝ => z u t) v) v :=
    (hxY.hasDerivAt.mul hyY.hasDerivAt).sub hzY.hasDerivAt
  have hdx :
      deriv (fun t : ℝ => w t v) u =
        deriv (fun t : ℝ => x t v) u * y u v +
          x u v * deriv (fun t : ℝ => y t v) u -
          deriv (fun t : ℝ => z t v) u := by
    calc
      deriv (fun t : ℝ => w t v) u =
          deriv (fun t : ℝ => x t v * y t v - z t v) u := hW_X.deriv_eq
      _ = _ := hDerivX.deriv
  have hdy :
      deriv (fun t : ℝ => w u t) v =
        deriv (fun t : ℝ => x u t) v * y u v +
          x u v * deriv (fun t : ℝ => y u t) v -
          deriv (fun t : ℝ => z u t) v := by
    calc
      deriv (fun t : ℝ => w u t) v =
          deriv (fun t : ℝ => x u t * y u t - z u t) v := hW_Y.deriv_eq
      _ = _ := hDerivY.deriv
  unfold differential partialX partialY
  rw [hdx, hdy]
  ring

theorem gap2 (x y z w : ℝ → ℝ → ℝ) (u v dx dy dz : ℝ) :
    differential w u v
        (z u v * dy + y u v * dz - dx)
        (z u v * dx + x u v * dz - dy) =
      partialX w u v * (z u v * dy + y u v * dz - dx) +
        partialY w u v * (z u v * dx + x u v * dz - dy) := by
  rfl

theorem gap3 (x y z w Z : ℝ → ℝ → ℝ) (u v dx dy : ℝ)
    (hEquation :
      y u v * dx + x u v * dy -
          differential Z (x u v) (y u v) dx dy =
        partialX w u v *
            (z u v * dy +
              y u v * differential Z (x u v) (y u v) dx dy - dx) +
          partialY w u v *
            (z u v * dx +
              x u v * differential Z (x u v) (y u v) dx dy - dy)) :
    solveDenominator x y w u v *
          differential Z (x u v) (y u v) dx dy =
      (y u v + partialX w u v - z u v * partialY w u v) * dx +
        (x u v + partialY w u v - z u v * partialX w u v) * dy := by
  unfold solveDenominator
  nlinarith [hEquation]

theorem gap4 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : solveDenominator x y w u v ≠ 0)
    (hForm : ∀ dx dy,
      solveDenominator x y w u v *
            differential Z (x u v) (y u v) dx dy =
        (y u v + partialX w u v - z u v * partialY w u v) * dx +
          (x u v + partialY w u v - z u v * partialX w u v) * dy) :
    partialX Z (x u v) (y u v) =
      (y u v + partialX w u v - z u v * partialY w u v) /
        solveDenominator x y w u v := by
  apply (eq_div_iff hDen).2
  simpa [differential, mul_comm] using hForm 1 0

theorem gap5 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : solveDenominator x y w u v ≠ 0)
    (hForm : ∀ dx dy,
      solveDenominator x y w u v *
            differential Z (x u v) (y u v) dx dy =
        (y u v + partialX w u v - z u v * partialY w u v) * dx +
          (x u v + partialY w u v - z u v * partialX w u v) * dy) :
    partialY Z (x u v) (y u v) =
      (x u v + partialY w u v - z u v * partialX w u v) /
        solveDenominator x y w u v := by
  apply (eq_div_iff hDen).2
  simpa [differential, mul_comm] using hForm 0 1

theorem gap6 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : solveDenominator x y w u v ≠ 0)
    (hPDE :
      (x u v * y u v + z u v) * partialX Z (x u v) (y u v) +
        (1 - y u v ^ 2) * partialY Z (x u v) (y u v) =
          x u v + y u v * z u v)
    (hZx : partialX Z (x u v) (y u v) =
      (y u v + partialX w u v - z u v * partialY w u v) /
        solveDenominator x y w u v)
    (hZy : partialY Z (x u v) (y u v) =
      (x u v + partialY w u v - z u v * partialX w u v) /
        solveDenominator x y w u v) :
    (x u v * y u v + z u v) *
          (y u v + partialX w u v - z u v * partialY w u v) +
        (1 - y u v ^ 2) *
          (x u v + partialY w u v - z u v * partialX w u v) =
      (x u v + y u v * z u v) * solveDenominator x y w u v := by
  rw [hZx, hZy] at hPDE
  field_simp [hDen] at hPDE
  nlinarith [hPDE]

theorem gap7 (x y z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hEquation :
      (x u v * y u v + z u v) *
            (y u v + partialX w u v - z u v * partialY w u v) +
          (1 - y u v ^ 2) *
            (x u v + partialY w u v - z u v * partialX w u v) =
        (x u v + y u v * z u v) * solveDenominator x y w u v) :
    (1 - x u v ^ 2 - y u v ^ 2 - z u v ^ 2 -
        2 * x u v * y u v * z u v) * partialY w u v = 0 := by
  unfold solveDenominator at hEquation
  nlinarith [hEquation]

theorem gap8 (x y z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hNondegenerate :
      1 - x u v ^ 2 - y u v ^ 2 - z u v ^ 2 -
        2 * x u v * y u v * z u v ≠ 0)
    (hProduct :
      (1 - x u v ^ 2 - y u v ^ 2 - z u v ^ 2 -
        2 * x u v * y u v * z u v) * partialY w u v = 0) :
    partialY w u v = 0 := by
  rcases mul_eq_zero.mp hProduct with hCoefficient | hPartial
  · exact (hNondegenerate hCoefficient).elim
  · exact hPartial

end

end ProofGap.Exercise3476
