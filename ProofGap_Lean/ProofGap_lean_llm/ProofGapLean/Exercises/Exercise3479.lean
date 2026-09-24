import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3479

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (u v du dv : ℝ) : ℝ :=
  partialX f u v * du + partialY f u v * dv

def solveDenominator (x y z w : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  1 + z u v - x u v * partialX w u v - y u v * partialY w u v

theorem gap1 (z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (u, v))
    (hwDiff : DifferentiableAt ℝ (Function.uncurry w) (u, v))
    (hW : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      w p.1 p.2 = z p.1 p.2 * Real.exp (z p.1 p.2)) :
    differential w u v du dv =
      Real.exp (z u v) * (1 + z u v) * differential z u v du dv := by
  have hiX : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u := by
    fun_prop
  have hiY : DifferentiableAt ℝ (fun t : ℝ => (u, t)) v := by
    fun_prop
  have hWx : (fun t : ℝ => w t v) =ᶠ[nhds u]
      (fun t : ℝ => z t v * Real.exp (z t v)) := by
    simpa using hiX.continuousAt.eventually hW
  have hWy : (fun t : ℝ => w u t) =ᶠ[nhds v]
      (fun t : ℝ => z u t * Real.exp (z u t)) := by
    simpa using hiY.continuousAt.eventually hW
  have hzX : DifferentiableAt ℝ (fun t : ℝ => z t v) u := by
    simpa [Function.comp_def] using hzDiff.comp u hiX
  have hzY : DifferentiableAt ℝ (fun t : ℝ => z u t) v := by
    simpa [Function.comp_def] using hzDiff.comp v hiY
  have hzX' : HasDerivAt (fun t : ℝ => z t v) (partialX z u v) u := by
    simpa [partialX] using hzX.hasDerivAt
  have hzY' : HasDerivAt (fun t : ℝ => z u t) (partialY z u v) v := by
    simpa [partialY] using hzY.hasDerivAt
  have hExpX : HasDerivAt (fun t : ℝ => Real.exp (z t v))
      (Real.exp (z u v) * partialX z u v) u := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (z u v)).comp u hzX'
  have hExpY : HasDerivAt (fun t : ℝ => Real.exp (z u t))
      (Real.exp (z u v) * partialY z u v) v := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (z u v)).comp v hzY'
  have hProdX : HasDerivAt (fun t : ℝ => z t v * Real.exp (z t v))
      (partialX z u v * Real.exp (z u v) +
        z u v * (Real.exp (z u v) * partialX z u v)) u :=
    hzX'.mul hExpX
  have hProdY : HasDerivAt (fun t : ℝ => z u t * Real.exp (z u t))
      (partialY z u v * Real.exp (z u v) +
        z u v * (Real.exp (z u v) * partialY z u v)) v :=
    hzY'.mul hExpY
  have hx : partialX w u v =
      Real.exp (z u v) * (1 + z u v) * partialX z u v := by
    calc
      partialX w u v =
          deriv (fun t : ℝ => z t v * Real.exp (z t v)) u := by
            simpa [partialX] using hWx.deriv_eq
      _ = partialX z u v * Real.exp (z u v) +
          z u v * (Real.exp (z u v) * partialX z u v) := hProdX.deriv
      _ = Real.exp (z u v) * (1 + z u v) * partialX z u v := by ring
  have hy : partialY w u v =
      Real.exp (z u v) * (1 + z u v) * partialY z u v := by
    calc
      partialY w u v =
          deriv (fun t : ℝ => z u t * Real.exp (z u t)) v := by
            simpa [partialY] using hWy.deriv_eq
      _ = partialY z u v * Real.exp (z u v) +
          z u v * (Real.exp (z u v) * partialY z u v) := hProdY.deriv
      _ = Real.exp (z u v) * (1 + z u v) * partialY z u v := by ring
  unfold differential
  rw [hx, hy]
  ring

theorem gap2 (z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hProduct : differential w u v du dv =
      Real.exp (z u v) * (1 + z u v) * differential z u v du dv) :
    Real.exp (z u v) * (1 + z u v) * differential z u v du dv =
      partialX w u v * du + partialY w u v * dv := by
  simpa [differential] using hProduct.symm

theorem gap3 (x y z w : ℝ → ℝ → ℝ) (u v du dv dx dy : ℝ)
    (hDu : du =
      Real.exp (z u v) * dx +
        x u v * Real.exp (z u v) * differential z u v dx dy)
    (hDv : dv =
      Real.exp (z u v) * dy +
        y u v * Real.exp (z u v) * differential z u v dx dy) :
    partialX w u v * du + partialY w u v * dv =
      partialX w u v *
          (Real.exp (z u v) * dx +
            x u v * Real.exp (z u v) * differential z u v dx dy) +
        partialY w u v *
          (Real.exp (z u v) * dy +
            y u v * Real.exp (z u v) * differential z u v dx dy) := by
  rw [hDu, hDv]

theorem gap4 (x y z w : ℝ → ℝ → ℝ) (u v dx dy : ℝ)
    (hLeft :
      differential w u v
          (Real.exp (z u v) * dx +
            x u v * Real.exp (z u v) * differential z u v dx dy)
          (Real.exp (z u v) * dy +
            y u v * Real.exp (z u v) * differential z u v dx dy) =
        Real.exp (z u v) * (1 + z u v) * differential z u v dx dy)
    (hRight :
      partialX w u v *
            (Real.exp (z u v) * dx +
              x u v * Real.exp (z u v) * differential z u v dx dy) +
          partialY w u v *
            (Real.exp (z u v) * dy +
              y u v * Real.exp (z u v) * differential z u v dx dy) =
        differential w u v
          (Real.exp (z u v) * dx +
            x u v * Real.exp (z u v) * differential z u v dx dy)
          (Real.exp (z u v) * dy +
            y u v * Real.exp (z u v) * differential z u v dx dy)) :
    Real.exp (z u v) * (1 + z u v) * differential z u v dx dy =
      partialX w u v *
          (Real.exp (z u v) * dx +
            x u v * Real.exp (z u v) * differential z u v dx dy) +
        partialY w u v *
          (Real.exp (z u v) * dy +
            y u v * Real.exp (z u v) * differential z u v dx dy) := by
  exact hLeft.symm.trans hRight.symm

theorem gap5 (x y z w Z : ℝ → ℝ → ℝ) (u v dx dy : ℝ)
    (hEquation :
      Real.exp (z u v) * (1 + z u v) *
            differential Z (x u v) (y u v) dx dy =
        partialX w u v *
            (Real.exp (z u v) * dx +
              x u v * Real.exp (z u v) *
                differential Z (x u v) (y u v) dx dy) +
          partialY w u v *
            (Real.exp (z u v) * dy +
              y u v * Real.exp (z u v) *
                differential Z (x u v) (y u v) dx dy)) :
    solveDenominator x y z w u v *
        differential Z (x u v) (y u v) dx dy =
      partialX w u v * dx + partialY w u v * dy := by
  have hscaled :
      Real.exp (z u v) *
          (solveDenominator x y z w u v *
              differential Z (x u v) (y u v) dx dy -
            (partialX w u v * dx + partialY w u v * dy)) = 0 := by
    unfold solveDenominator
    calc
      Real.exp (z u v) *
          ((1 + z u v - x u v * partialX w u v -
                y u v * partialY w u v) *
              differential Z (x u v) (y u v) dx dy -
            (partialX w u v * dx + partialY w u v * dy)) =
          Real.exp (z u v) * (1 + z u v) *
              differential Z (x u v) (y u v) dx dy -
            (partialX w u v *
                (Real.exp (z u v) * dx +
                  x u v * Real.exp (z u v) *
                    differential Z (x u v) (y u v) dx dy) +
              partialY w u v *
                (Real.exp (z u v) * dy +
                  y u v * Real.exp (z u v) *
                    differential Z (x u v) (y u v) dx dy)) := by ring
      _ = 0 := by rw [hEquation]; ring
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp hscaled).resolve_left (Real.exp_ne_zero (z u v))

theorem gap6 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : solveDenominator x y z w u v ≠ 0)
    (hForm : ∀ dx dy,
      solveDenominator x y z w u v *
          differential Z (x u v) (y u v) dx dy =
        partialX w u v * dx + partialY w u v * dy) :
    partialX Z (x u v) (y u v) =
      partialX w u v / solveDenominator x y z w u v := by
  apply (eq_div_iff hDen).2
  have h := hForm 1 0
  simpa [differential, mul_comm] using h

theorem gap7 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : solveDenominator x y z w u v ≠ 0)
    (hForm : ∀ dx dy,
      solveDenominator x y z w u v *
          differential Z (x u v) (y u v) dx dy =
        partialX w u v * dx + partialY w u v * dy) :
    partialY Z (x u v) (y u v) =
      partialY w u v / solveDenominator x y z w u v := by
  apply (eq_div_iff hDen).2
  have h := hForm 0 1
  simpa [differential, mul_comm] using h

theorem gap8 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : solveDenominator x y z w u v ≠ 0)
    (hwv : partialY w u v ≠ 0)
    (hZx : partialX Z (x u v) (y u v) =
      partialX w u v / solveDenominator x y z w u v)
    (hZy : partialY Z (x u v) (y u v) =
      partialY w u v / solveDenominator x y z w u v) :
    partialX Z (x u v) (y u v) / partialY Z (x u v) (y u v) =
      partialX w u v / partialY w u v := by
  rw [hZx, hZy]
  field_simp [hDen, hwv]

end

end ProofGap.Exercise3479
