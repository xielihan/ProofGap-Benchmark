import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace ProofGap.Exercise3475

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (u v du dv : ℝ) : ℝ :=
  partialX f u v * du + partialY f u v * dv

private abbrev Tendsto {α β : Type*} (m : α → β) (f : Filter α) (g : Filter β) : Prop :=
  Filter.Tendsto m f g

private theorem _root_.Continuous.prod_mk
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {f : α → β} {g : α → γ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (f x, g x)) :=
  hf.prodMk hg

theorem gap1 (x : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (u, v), p.1 = x p.1 p.2) :
    du = differential x u v du dv := by
  have hUx :
      (fun t : ℝ => t) =ᶠ[nhds u] (fun t => x t v) := by
    have ht :
        Tendsto (fun t : ℝ => (t, v)) (nhds u) (nhds (u, v)) :=
      (continuous_id.prod_mk continuous_const).continuousAt
    simpa using ht hU
  have hUy :
      (fun _ : ℝ => u) =ᶠ[nhds v] (fun t => x u t) := by
    have ht :
        Tendsto (fun t : ℝ => (u, t)) (nhds v) (nhds (u, v)) :=
      (continuous_const.prod_mk continuous_id).continuousAt
    simpa using ht hU
  have hpx : partialX x u v = 1 := by
    unfold partialX
    rw [← hUx.deriv_eq]
    simpa using (hasDerivAt_id u).deriv
  have hpy : partialY x u v = 0 := by
    unfold partialY
    rw [← hUy.deriv_eq]
    simp
  simp [differential, hpx, hpy]

theorem gap2 (x y : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hx : x u v ≠ 0) (hy : y u v ≠ 0)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      p.2 = 1 / y p.1 p.2 - 1 / x p.1 p.2) :
    dv =
      1 / x u v ^ 2 * differential x u v du dv -
        1 / y u v ^ 2 * differential y u v du dv := by
  have hidX : DifferentiableAt ℝ (fun t : ℝ => t) u :=
    differentiableAt_id
  have hconstX : DifferentiableAt ℝ (fun _ : ℝ => v) u :=
    differentiableAt_const v
  have hPairX : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u :=
    hidX.prodMk hconstX
  have hidY : DifferentiableAt ℝ (fun t : ℝ => t) v :=
    differentiableAt_id
  have hconstY : DifferentiableAt ℝ (fun _ : ℝ => u) v :=
    differentiableAt_const u
  have hPairY : DifferentiableAt ℝ (fun t : ℝ => (u, t)) v :=
    hconstY.prodMk hidY
  have hxX : DifferentiableAt ℝ (fun t => x t v) u := by
    change DifferentiableAt ℝ (Function.uncurry x ∘ fun t : ℝ => (t, v)) u
    exact hxDiff.comp u hPairX
  have hyX : DifferentiableAt ℝ (fun t => y t v) u := by
    change DifferentiableAt ℝ (Function.uncurry y ∘ fun t : ℝ => (t, v)) u
    exact hyDiff.comp u hPairX
  have hxY : DifferentiableAt ℝ (fun t => x u t) v := by
    change DifferentiableAt ℝ (Function.uncurry x ∘ fun t : ℝ => (u, t)) v
    exact hxDiff.comp v hPairY
  have hyY : DifferentiableAt ℝ (fun t => y u t) v := by
    change DifferentiableAt ℝ (Function.uncurry y ∘ fun t : ℝ => (u, t)) v
    exact hyDiff.comp v hPairY
  have hVX :
      (fun _ : ℝ => v) =ᶠ[nhds u]
        (fun t => 1 / y t v - 1 / x t v) := by
    simpa using hPairX.continuousAt hV
  have hVY :
      (fun t : ℝ => t) =ᶠ[nhds v]
        (fun t => 1 / y u t - 1 / x u t) := by
    simpa using hPairY.continuousAt hV
  have hRhsX :
      deriv (fun t => 1 / y t v - 1 / x t v) u =
        1 / x u v ^ 2 * partialX x u v -
          1 / y u v ^ 2 * partialX y u v := by
    unfold partialX
    have h :=
      ((hyX.hasDerivAt.inv hy).sub
        (hxX.hasDerivAt.inv hx)).deriv
    have hfun :
        (fun t : ℝ => 1 / y t v - 1 / x t v) =
          ((fun t : ℝ => y t v)⁻¹ -
            (fun t : ℝ => x t v)⁻¹) := by
      funext t
      simp [one_div]
    calc
      deriv (fun t => 1 / y t v - 1 / x t v) u =
          deriv ((fun t : ℝ => y t v)⁻¹ -
            (fun t : ℝ => x t v)⁻¹) u :=
        congrArg (fun f : ℝ → ℝ => deriv f u) hfun
      _ = -deriv (fun t => y t v) u / y u v ^ 2 -
          -deriv (fun t => x t v) u / x u v ^ 2 := h
      _ = 1 / x u v ^ 2 * deriv (fun t => x t v) u -
          1 / y u v ^ 2 * deriv (fun t => y t v) u := by
        simp only [one_div]
        ring
  have hRhsY :
      deriv (fun t => 1 / y u t - 1 / x u t) v =
        1 / x u v ^ 2 * partialY x u v -
          1 / y u v ^ 2 * partialY y u v := by
    unfold partialY
    have h :=
      ((hyY.hasDerivAt.inv hy).sub
        (hxY.hasDerivAt.inv hx)).deriv
    have hfun :
        (fun t : ℝ => 1 / y u t - 1 / x u t) =
          ((fun t : ℝ => y u t)⁻¹ -
            (fun t : ℝ => x u t)⁻¹) := by
      funext t
      simp [one_div]
    calc
      deriv (fun t => 1 / y u t - 1 / x u t) v =
          deriv ((fun t : ℝ => y u t)⁻¹ -
            (fun t : ℝ => x u t)⁻¹) v :=
        congrArg (fun f : ℝ → ℝ => deriv f v) hfun
      _ = -deriv (fun t => y u t) v / y u v ^ 2 -
          -deriv (fun t => x u t) v / x u v ^ 2 := h
      _ = 1 / x u v ^ 2 * deriv (fun t => x u t) v -
          1 / y u v ^ 2 * deriv (fun t => y u t) v := by
        simp only [one_div]
        ring
  have hCoeffX :
      1 / x u v ^ 2 * partialX x u v -
          1 / y u v ^ 2 * partialX y u v = 0 := by
    calc
      _ = deriv (fun t => 1 / y t v - 1 / x t v) u := hRhsX.symm
      _ = deriv (fun _ : ℝ => v) u := hVX.deriv_eq.symm
      _ = 0 := by simp
  have hCoeffY :
      1 / x u v ^ 2 * partialY x u v -
          1 / y u v ^ 2 * partialY y u v = 1 := by
    calc
      _ = deriv (fun t => 1 / y u t - 1 / x u t) v := hRhsY.symm
      _ = deriv (fun t : ℝ => t) v := hVY.deriv_eq.symm
      _ = 1 := by simpa using (hasDerivAt_id v).deriv
  unfold differential
  calc
    dv =
        (1 / x u v ^ 2 * partialX x u v -
            1 / y u v ^ 2 * partialX y u v) * du +
          (1 / x u v ^ 2 * partialY x u v -
            1 / y u v ^ 2 * partialY y u v) * dv := by
      rw [hCoeffX, hCoeffY]
      ring
    _ =
        1 / x u v ^ 2 *
            (partialX x u v * du + partialY x u v * dv) -
          1 / y u v ^ 2 *
            (partialX y u v * du + partialY y u v * dv) := by
      ring

theorem gap3 (x z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hx : x u v ≠ 0) (hz : z u v ≠ 0)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (u, v))
    (hwDiff : DifferentiableAt ℝ (Function.uncurry w) (u, v))
    (hW : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      w p.1 p.2 = 1 / z p.1 p.2 - 1 / x p.1 p.2) :
    differential w u v du dv =
      1 / x u v ^ 2 * differential x u v du dv -
        1 / z u v ^ 2 * differential z u v du dv := by
  have hidX : DifferentiableAt ℝ (fun t : ℝ => t) u :=
    differentiableAt_id
  have hconstX : DifferentiableAt ℝ (fun _ : ℝ => v) u :=
    differentiableAt_const v
  have hPairX : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u :=
    hidX.prodMk hconstX
  have hidY : DifferentiableAt ℝ (fun t : ℝ => t) v :=
    differentiableAt_id
  have hconstY : DifferentiableAt ℝ (fun _ : ℝ => u) v :=
    differentiableAt_const u
  have hPairY : DifferentiableAt ℝ (fun t : ℝ => (u, t)) v :=
    hconstY.prodMk hidY
  have hxX : DifferentiableAt ℝ (fun t => x t v) u := by
    change DifferentiableAt ℝ (Function.uncurry x ∘ fun t : ℝ => (t, v)) u
    exact hxDiff.comp u hPairX
  have hzX : DifferentiableAt ℝ (fun t => z t v) u := by
    change DifferentiableAt ℝ (Function.uncurry z ∘ fun t : ℝ => (t, v)) u
    exact hzDiff.comp u hPairX
  have hxY : DifferentiableAt ℝ (fun t => x u t) v := by
    change DifferentiableAt ℝ (Function.uncurry x ∘ fun t : ℝ => (u, t)) v
    exact hxDiff.comp v hPairY
  have hzY : DifferentiableAt ℝ (fun t => z u t) v := by
    change DifferentiableAt ℝ (Function.uncurry z ∘ fun t : ℝ => (u, t)) v
    exact hzDiff.comp v hPairY
  have hWX :
      (fun t => w t v) =ᶠ[nhds u]
        (fun t => 1 / z t v - 1 / x t v) := by
    simpa using hPairX.continuousAt hW
  have hWY :
      (fun t => w u t) =ᶠ[nhds v]
        (fun t => 1 / z u t - 1 / x u t) := by
    simpa using hPairY.continuousAt hW
  have hRhsX :
      deriv (fun t => 1 / z t v - 1 / x t v) u =
        1 / x u v ^ 2 * partialX x u v -
          1 / z u v ^ 2 * partialX z u v := by
    unfold partialX
    have h :=
      ((hzX.hasDerivAt.inv hz).sub
        (hxX.hasDerivAt.inv hx)).deriv
    have hfun :
        (fun t : ℝ => 1 / z t v - 1 / x t v) =
          ((fun t : ℝ => z t v)⁻¹ -
            (fun t : ℝ => x t v)⁻¹) := by
      funext t
      simp [one_div]
    calc
      deriv (fun t => 1 / z t v - 1 / x t v) u =
          deriv ((fun t : ℝ => z t v)⁻¹ -
            (fun t : ℝ => x t v)⁻¹) u :=
        congrArg (fun f : ℝ → ℝ => deriv f u) hfun
      _ = -deriv (fun t => z t v) u / z u v ^ 2 -
          -deriv (fun t => x t v) u / x u v ^ 2 := h
      _ = 1 / x u v ^ 2 * deriv (fun t => x t v) u -
          1 / z u v ^ 2 * deriv (fun t => z t v) u := by
        simp only [one_div]
        ring
  have hRhsY :
      deriv (fun t => 1 / z u t - 1 / x u t) v =
        1 / x u v ^ 2 * partialY x u v -
          1 / z u v ^ 2 * partialY z u v := by
    unfold partialY
    have h :=
      ((hzY.hasDerivAt.inv hz).sub
        (hxY.hasDerivAt.inv hx)).deriv
    have hfun :
        (fun t : ℝ => 1 / z u t - 1 / x u t) =
          ((fun t : ℝ => z u t)⁻¹ -
            (fun t : ℝ => x u t)⁻¹) := by
      funext t
      simp [one_div]
    calc
      deriv (fun t => 1 / z u t - 1 / x u t) v =
          deriv ((fun t : ℝ => z u t)⁻¹ -
            (fun t : ℝ => x u t)⁻¹) v :=
        congrArg (fun f : ℝ → ℝ => deriv f v) hfun
      _ = -deriv (fun t => z u t) v / z u v ^ 2 -
          -deriv (fun t => x u t) v / x u v ^ 2 := h
      _ = 1 / x u v ^ 2 * deriv (fun t => x u t) v -
          1 / z u v ^ 2 * deriv (fun t => z u t) v := by
        simp only [one_div]
        ring
  have hpX :
      partialX w u v =
        1 / x u v ^ 2 * partialX x u v -
          1 / z u v ^ 2 * partialX z u v := by
    unfold partialX
    calc
      deriv (fun t => w t v) u =
          deriv (fun t => 1 / z t v - 1 / x t v) u := hWX.deriv_eq
      _ = _ := hRhsX
  have hpY :
      partialY w u v =
        1 / x u v ^ 2 * partialY x u v -
          1 / z u v ^ 2 * partialY z u v := by
    unfold partialY
    calc
      deriv (fun t => w u t) v =
          deriv (fun t => 1 / z u t - 1 / x u t) v := hWY.deriv_eq
      _ = _ := hRhsY
  unfold differential
  rw [hpX, hpY]
  ring

theorem gap4 (x y z w Z : ℝ → ℝ → ℝ) (u v dx dy : ℝ)
    (hReciprocal :
      1 / x u v ^ 2 * dx -
          1 / z u v ^ 2 * differential Z (x u v) (y u v) dx dy =
        differential w u v dx
          (1 / x u v ^ 2 * dx - 1 / y u v ^ 2 * dy))
    (hTotal :
      differential w u v dx
          (1 / x u v ^ 2 * dx - 1 / y u v ^ 2 * dy) =
        partialX w u v * dx +
          partialY w u v *
            (1 / x u v ^ 2 * dx - 1 / y u v ^ 2 * dy)) :
    1 / x u v ^ 2 * dx -
        1 / z u v ^ 2 * differential Z (x u v) (y u v) dx dy =
      partialX w u v * dx +
        partialY w u v *
          (1 / x u v ^ 2 * dx - 1 / y u v ^ 2 * dy) := by
  exact hReciprocal.trans hTotal

theorem gap5 (x y z w Z : ℝ → ℝ → ℝ) (u v dx dy : ℝ)
    (hz : z u v ≠ 0)
    (hEquation :
      1 / x u v ^ 2 * dx -
          1 / z u v ^ 2 * differential Z (x u v) (y u v) dx dy =
        partialX w u v * dx +
          partialY w u v *
            (1 / x u v ^ 2 * dx - 1 / y u v ^ 2 * dy)) :
    differential Z (x u v) (y u v) dx dy =
      z u v ^ 2 *
          (1 / x u v ^ 2 - partialX w u v -
            1 / x u v ^ 2 * partialY w u v) * dx +
        z u v ^ 2 / y u v ^ 2 * partialY w u v * dy := by
  have hsolve :
      1 / z u v ^ 2 * differential Z (x u v) (y u v) dx dy =
        1 / x u v ^ 2 * dx -
          (partialX w u v * dx +
            partialY w u v *
              (1 / x u v ^ 2 * dx - 1 / y u v ^ 2 * dy)) := by
    linarith [hEquation]
  calc
    differential Z (x u v) (y u v) dx dy =
        z u v ^ 2 *
          (1 / z u v ^ 2 *
            differential Z (x u v) (y u v) dx dy) := by
      field_simp [hz]
    _ = z u v ^ 2 *
          (1 / x u v ^ 2 * dx -
            (partialX w u v * dx +
              partialY w u v *
                (1 / x u v ^ 2 * dx - 1 / y u v ^ 2 * dy))) := by
      rw [hsolve]
    _ =
        z u v ^ 2 *
            (1 / x u v ^ 2 - partialX w u v -
              1 / x u v ^ 2 * partialY w u v) * dx +
          z u v ^ 2 / y u v ^ 2 * partialY w u v * dy := by
      ring

theorem gap6 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hForm : ∀ dx dy,
      differential Z (x u v) (y u v) dx dy =
        z u v ^ 2 *
            (1 / x u v ^ 2 - partialX w u v -
              1 / x u v ^ 2 * partialY w u v) * dx +
          z u v ^ 2 / y u v ^ 2 * partialY w u v * dy) :
    partialX Z (x u v) (y u v) =
      z u v ^ 2 *
        (1 / x u v ^ 2 - partialX w u v -
          1 / x u v ^ 2 * partialY w u v) := by
  simpa [differential] using hForm 1 0

theorem gap7 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hForm : ∀ dx dy,
      differential Z (x u v) (y u v) dx dy =
        z u v ^ 2 *
            (1 / x u v ^ 2 - partialX w u v -
              1 / x u v ^ 2 * partialY w u v) * dx +
          z u v ^ 2 / y u v ^ 2 * partialY w u v * dy) :
    partialY Z (x u v) (y u v) =
      z u v ^ 2 / y u v ^ 2 * partialY w u v := by
  simpa [differential] using hForm 0 1

theorem gap8 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hx : x u v ≠ 0) (hy : y u v ≠ 0)
    (hPDE :
      x u v ^ 2 * partialX Z (x u v) (y u v) +
        y u v ^ 2 * partialY Z (x u v) (y u v) = z u v ^ 2)
    (hZx : partialX Z (x u v) (y u v) =
      z u v ^ 2 *
        (1 / x u v ^ 2 - partialX w u v -
          1 / x u v ^ 2 * partialY w u v))
    (hZy : partialY Z (x u v) (y u v) =
      z u v ^ 2 / y u v ^ 2 * partialY w u v) :
    z u v ^ 2 *
          (1 - x u v ^ 2 * partialX w u v - partialY w u v) +
        z u v ^ 2 * partialY w u v =
      z u v ^ 2 := by
  calc
    z u v ^ 2 *
          (1 - x u v ^ 2 * partialX w u v - partialY w u v) +
        z u v ^ 2 * partialY w u v =
      x u v ^ 2 * partialX Z (x u v) (y u v) +
        y u v ^ 2 * partialY Z (x u v) (y u v) := by
      rw [hZx, hZy]
      field_simp [hx, hy] <;> ring
    _ = z u v ^ 2 := hPDE

theorem gap9 (x z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hEquation :
      z u v ^ 2 *
            (1 - x u v ^ 2 * partialX w u v - partialY w u v) +
          z u v ^ 2 * partialY w u v =
        z u v ^ 2) :
    x u v ^ 2 * z u v ^ 2 * partialX w u v = 0 := by
  nlinarith [hEquation]

theorem gap10 (x z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hx : x u v ≠ 0) (hz : z u v ≠ 0)
    (hProduct : x u v ^ 2 * z u v ^ 2 * partialX w u v = 0) :
    partialX w u v = 0 := by
  exact
    (mul_eq_zero.mp hProduct).resolve_left
      (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hz))

end

end ProofGap.Exercise3475
