import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3477

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (u v du dv : ℝ) : ℝ :=
  partialX f u v * du + partialY f u v * dv

def solveDenominator (w : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  1 + u * partialX w u v + v * partialY w u v

theorem gap1 (x w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hwDiff : DifferentiableAt ℝ (Function.uncurry w) (u, v))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      x p.1 p.2 = p.1 * Real.exp (w p.1 p.2)) :
    differential x u v du dv =
      Real.exp (w u v) * du +
        u * Real.exp (w u v) * differential w u v du dv := by
  have hXx :
      (fun t : ℝ => x t v) =ᶠ[nhds u]
        (fun t : ℝ => t * Real.exp (w t v)) := by
    exact (continuousAt_id.prodMk continuousAt_const).eventually hX
  have hXy :
      (fun t : ℝ => x u t) =ᶠ[nhds v]
        (fun t : ℝ => u * Real.exp (w u t)) := by
    exact (continuousAt_const.prodMk continuousAt_id).eventually hX
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u := by
    have hid : DifferentiableAt ℝ (fun t : ℝ => t) u := differentiableAt_id
    have hc : DifferentiableAt ℝ (fun _ : ℝ => v) u :=
      differentiableAt_const (c := v)
    exact hid.prodMk hc
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (u, t)) v := by
    have hc : DifferentiableAt ℝ (fun _ : ℝ => u) v :=
      differentiableAt_const (c := u)
    have hid : DifferentiableAt ℝ (fun t : ℝ => t) v := differentiableAt_id
    exact hc.prodMk hid
  have hwx : DifferentiableAt ℝ (fun t : ℝ => w t v) u := by
    simpa using hwDiff.comp u hpairX
  have hwy : DifferentiableAt ℝ (fun t : ℝ => w u t) v := by
    simpa using hwDiff.comp v hpairY
  have hdx :
      deriv (fun t : ℝ => t * Real.exp (w t v)) u =
        Real.exp (w u v) +
          u * (Real.exp (w u v) * deriv (fun t : ℝ => w t v) u) := by
    simpa using
      (((hasDerivAt_id u).mul (hwx.hasDerivAt.exp)).deriv)
  have hdy :
      deriv (fun t : ℝ => u * Real.exp (w u t)) v =
        u * (Real.exp (w u v) * deriv (fun t : ℝ => w u t) v) := by
    simpa using (((hwy.hasDerivAt.exp).const_mul u).deriv)
  unfold differential partialX partialY
  rw [hXx.deriv_eq, hXy.deriv_eq, hdx, hdy]
  ring

theorem gap2 (y w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hwDiff : DifferentiableAt ℝ (Function.uncurry w) (u, v))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      y p.1 p.2 = p.2 * Real.exp (w p.1 p.2)) :
    differential y u v du dv =
      Real.exp (w u v) * dv +
        v * Real.exp (w u v) * differential w u v du dv := by
  have hYx :
      (fun t : ℝ => y t v) =ᶠ[nhds u]
        (fun t : ℝ => v * Real.exp (w t v)) := by
    exact (continuousAt_id.prodMk continuousAt_const).eventually hY
  have hYy :
      (fun t : ℝ => y u t) =ᶠ[nhds v]
        (fun t : ℝ => t * Real.exp (w u t)) := by
    exact (continuousAt_const.prodMk continuousAt_id).eventually hY
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u := by
    have hid : DifferentiableAt ℝ (fun t : ℝ => t) u := differentiableAt_id
    have hc : DifferentiableAt ℝ (fun _ : ℝ => v) u :=
      differentiableAt_const (c := v)
    exact hid.prodMk hc
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (u, t)) v := by
    have hc : DifferentiableAt ℝ (fun _ : ℝ => u) v :=
      differentiableAt_const (c := u)
    have hid : DifferentiableAt ℝ (fun t : ℝ => t) v := differentiableAt_id
    exact hc.prodMk hid
  have hwx : DifferentiableAt ℝ (fun t : ℝ => w t v) u := by
    simpa using hwDiff.comp u hpairX
  have hwy : DifferentiableAt ℝ (fun t : ℝ => w u t) v := by
    simpa using hwDiff.comp v hpairY
  have hdx :
      deriv (fun t : ℝ => v * Real.exp (w t v)) u =
        v * (Real.exp (w u v) * deriv (fun t : ℝ => w t v) u) := by
    simpa using (((hwx.hasDerivAt.exp).const_mul v).deriv)
  have hdy :
      deriv (fun t : ℝ => t * Real.exp (w u t)) v =
        Real.exp (w u v) +
          v * (Real.exp (w u v) * deriv (fun t : ℝ => w u t) v) := by
    simpa using
      (((hasDerivAt_id v).mul (hwy.hasDerivAt.exp)).deriv)
  unfold differential partialX partialY
  rw [hYx.deriv_eq, hYy.deriv_eq, hdx, hdy]
  ring

theorem gap3 (z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (u, v))
    (hwDiff : DifferentiableAt ℝ (Function.uncurry w) (u, v))
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      z p.1 p.2 = w p.1 p.2 * Real.exp (w p.1 p.2)) :
    differential z u v du dv =
      Real.exp (w u v) * (1 + w u v) * differential w u v du dv := by
  have hZx :
      (fun t : ℝ => z t v) =ᶠ[nhds u]
        (fun t : ℝ => w t v * Real.exp (w t v)) := by
    exact (continuousAt_id.prodMk continuousAt_const).eventually hZ
  have hZy :
      (fun t : ℝ => z u t) =ᶠ[nhds v]
        (fun t : ℝ => w u t * Real.exp (w u t)) := by
    exact (continuousAt_const.prodMk continuousAt_id).eventually hZ
  have hpairX : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u := by
    have hid : DifferentiableAt ℝ (fun t : ℝ => t) u := differentiableAt_id
    have hc : DifferentiableAt ℝ (fun _ : ℝ => v) u :=
      differentiableAt_const (c := v)
    exact hid.prodMk hc
  have hpairY : DifferentiableAt ℝ (fun t : ℝ => (u, t)) v := by
    have hc : DifferentiableAt ℝ (fun _ : ℝ => u) v :=
      differentiableAt_const (c := u)
    have hid : DifferentiableAt ℝ (fun t : ℝ => t) v := differentiableAt_id
    exact hc.prodMk hid
  have hwx : DifferentiableAt ℝ (fun t : ℝ => w t v) u := by
    simpa using hwDiff.comp u hpairX
  have hwy : DifferentiableAt ℝ (fun t : ℝ => w u t) v := by
    simpa using hwDiff.comp v hpairY
  have hdx :
      deriv (fun t : ℝ => w t v * Real.exp (w t v)) u =
        deriv (fun t : ℝ => w t v) u * Real.exp (w u v) +
          w u v * (Real.exp (w u v) * deriv (fun t : ℝ => w t v) u) := by
    simpa using ((hwx.hasDerivAt.mul hwx.hasDerivAt.exp).deriv)
  have hdy :
      deriv (fun t : ℝ => w u t * Real.exp (w u t)) v =
        deriv (fun t : ℝ => w u t) v * Real.exp (w u v) +
          w u v * (Real.exp (w u v) * deriv (fun t : ℝ => w u t) v) := by
    simpa using ((hwy.hasDerivAt.mul hwy.hasDerivAt.exp).deriv)
  unfold differential partialX partialY
  rw [hZx.deriv_eq, hZy.deriv_eq, hdx, hdy]
  ring

theorem gap4 (z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hFactor : 1 + w u v ≠ 0)
    (hDz : differential z u v du dv =
      Real.exp (w u v) * (1 + w u v) * differential w u v du dv) :
    Real.exp (w u v) * differential w u v du dv =
      differential z u v du dv / (1 + w u v) := by
  apply (eq_div_iff hFactor).2
  rw [hDz]
  ring

theorem gap5 (x z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hDx : differential x u v du dv =
      Real.exp (w u v) * du +
        u * Real.exp (w u v) * differential w u v du dv)
    (hScaled : Real.exp (w u v) * differential w u v du dv =
      differential z u v du dv / (1 + w u v)) :
    Real.exp (w u v) * du =
      differential x u v du dv -
        u / (1 + w u v) * differential z u v du dv := by
  calc
    Real.exp (w u v) * du =
        differential x u v du dv -
          u * (Real.exp (w u v) * differential w u v du dv) := by
      rw [hDx]
      ring
    _ = differential x u v du dv -
          u * (differential z u v du dv / (1 + w u v)) := by
      rw [hScaled]
    _ = differential x u v du dv -
          u / (1 + w u v) * differential z u v du dv := by
      ring

theorem gap6 (y z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hDy : differential y u v du dv =
      Real.exp (w u v) * dv +
        v * Real.exp (w u v) * differential w u v du dv)
    (hScaled : Real.exp (w u v) * differential w u v du dv =
      differential z u v du dv / (1 + w u v)) :
    Real.exp (w u v) * dv =
      differential y u v du dv -
        v / (1 + w u v) * differential z u v du dv := by
  calc
    Real.exp (w u v) * dv =
        differential y u v du dv -
          v * (Real.exp (w u v) * differential w u v du dv) := by
      rw [hDy]
      ring
    _ = differential y u v du dv -
          v * (differential z u v du dv / (1 + w u v)) := by
      rw [hScaled]
    _ = differential y u v du dv -
          v / (1 + w u v) * differential z u v du dv := by
      ring

theorem gap7 (x y z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hScaledW : Real.exp (w u v) * differential w u v du dv =
      differential z u v du dv / (1 + w u v))
    (hScaledU : Real.exp (w u v) * du =
      differential x u v du dv -
        u / (1 + w u v) * differential z u v du dv)
    (hScaledV : Real.exp (w u v) * dv =
      differential y u v du dv -
        v / (1 + w u v) * differential z u v du dv) :
    differential z u v du dv / (1 + w u v) =
      partialX w u v *
          (differential x u v du dv -
            u / (1 + w u v) * differential z u v du dv) +
        partialY w u v *
          (differential y u v du dv -
            v / (1 + w u v) * differential z u v du dv) := by
  calc
    differential z u v du dv / (1 + w u v) =
        Real.exp (w u v) * differential w u v du dv := hScaledW.symm
    _ = partialX w u v * (Real.exp (w u v) * du) +
          partialY w u v * (Real.exp (w u v) * dv) := by
      unfold differential
      ring
    _ = partialX w u v *
          (differential x u v du dv -
            u / (1 + w u v) * differential z u v du dv) +
        partialY w u v *
          (differential y u v du dv -
            v / (1 + w u v) * differential z u v du dv) := by
      rw [hScaledU, hScaledV]

theorem gap8 (x y z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hFactor : 1 + w u v ≠ 0)
    (hEquation :
      differential z u v du dv / (1 + w u v) =
        partialX w u v *
            (differential x u v du dv -
              u / (1 + w u v) * differential z u v du dv) +
          partialY w u v *
            (differential y u v du dv -
              v / (1 + w u v) * differential z u v du dv)) :
    solveDenominator w u v * differential z u v du dv =
      (1 + w u v) * partialX w u v * differential x u v du dv +
        (1 + w u v) * partialY w u v * differential y u v du dv := by
  field_simp [hFactor] at hEquation
  unfold solveDenominator
  ring_nf at hEquation ⊢
  linarith

theorem gap9 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : solveDenominator w u v ≠ 0)
    (hX : x u v = u * Real.exp (w u v))
    (hY : y u v = v * Real.exp (w u v))
    (hZ : z u v = w u v * Real.exp (w u v))
    (hZx : partialX Z (x u v) (y u v) =
      (1 + w u v) * partialX w u v / solveDenominator w u v)
    (hZy : partialY Z (x u v) (y u v) =
      (1 + w u v) * partialY w u v / solveDenominator w u v)
    (hPDE :
      (x u v * partialX Z (x u v) (y u v)) ^ 2 +
          (y u v * partialY Z (x u v) (y u v)) ^ 2 =
        z u v ^ 2 * partialX Z (x u v) (y u v) *
          partialY Z (x u v) (y u v)) :
    (u * Real.exp (w u v) * (1 + w u v) * partialX w u v) ^ 2 +
        (v * Real.exp (w u v) * (1 + w u v) * partialY w u v) ^ 2 =
      (w u v * Real.exp (w u v)) ^ 2 * (1 + w u v) ^ 2 *
        partialX w u v * partialY w u v := by
  rw [hZx, hZy, hX, hY, hZ] at hPDE
  field_simp [hDen] at hPDE
  calc
    (u * Real.exp (w u v) * (1 + w u v) * partialX w u v) ^ 2 +
          (v * Real.exp (w u v) * (1 + w u v) * partialY w u v) ^ 2 =
        Real.exp (w u v) ^ 2 *
          ((1 + w u v) ^ 2 *
            (u ^ 2 * partialX w u v ^ 2 +
              v ^ 2 * partialY w u v ^ 2)) := by
      ring
    _ = Real.exp (w u v) ^ 2 *
          (w u v ^ 2 * (1 + w u v) ^ 2 *
            partialX w u v * partialY w u v) := by
      rw [hPDE]
    _ = (w u v * Real.exp (w u v)) ^ 2 * (1 + w u v) ^ 2 *
          partialX w u v * partialY w u v := by
      ring

theorem gap10 (w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hFactor : 1 + w u v ≠ 0)
    (hEquation :
      (u * Real.exp (w u v) * (1 + w u v) * partialX w u v) ^ 2 +
          (v * Real.exp (w u v) * (1 + w u v) * partialY w u v) ^ 2 =
        (w u v * Real.exp (w u v)) ^ 2 * (1 + w u v) ^ 2 *
          partialX w u v * partialY w u v) :
    u ^ 2 * partialX w u v ^ 2 + v ^ 2 * partialY w u v ^ 2 =
      w u v ^ 2 * partialX w u v * partialY w u v := by
  have hCommon :
      (Real.exp (w u v) * (1 + w u v)) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (mul_ne_zero (Real.exp_ne_zero _) hFactor)
  have hEq :
      (Real.exp (w u v) * (1 + w u v)) ^ 2 *
          (u ^ 2 * partialX w u v ^ 2 +
            v ^ 2 * partialY w u v ^ 2) =
        (Real.exp (w u v) * (1 + w u v)) ^ 2 *
          (w u v ^ 2 * partialX w u v * partialY w u v) := by
    convert hEquation using 1 <;> ring
  exact mul_left_cancel₀ hCommon hEq

end

end ProofGap.Exercise3477
