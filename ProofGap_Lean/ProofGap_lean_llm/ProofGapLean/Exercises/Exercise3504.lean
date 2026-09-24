import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise3504

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialX f) x y
def d1 (f : ℝ → ℝ) (u : ℝ) : ℝ := deriv f u
def d2 (f : ℝ → ℝ) (u : ℝ) : ℝ := deriv (deriv f) u

private theorem hasDerivAt_comp_local
    {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hg : HasDerivAt g g' x)
    (hf : HasDerivAt f f' (g x)) :
    HasDerivAt (fun z => f (g z)) (g' * f') x := by
  have hpure : Filter.Tendsto g (pure x) (pure (g x)) := by
    simp [Filter.Tendsto]
  have hmap : Filter.Tendsto (Prod.map g g)
      (nhds x ×ˢ pure x) (nhds (g x) ×ˢ pure (g x)) :=
    Filter.Tendsto.prodMap hg.continuousAt hpure
  have hc := hf.comp hg hmap
  have hclm :
      (ContinuousLinearMap.toSpanSingleton ℝ f').comp
          (ContinuousLinearMap.toSpanSingleton ℝ g') =
        ContinuousLinearMap.toSpanSingleton ℝ (g' * f') := by
    apply ContinuousLinearMap.ext
    intro z
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [hclm] at hc
  simpa [HasDerivAt, HasFDerivAt, Function.comp_def] using hc

theorem gap1 (u w : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (x₀ y₀ x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y), w p.1 p.2 = f (u p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = (p.1 - x₀) * (p.2 - y₀))
    (hDifff : DifferentiableAt ℝ f (u x y)) :
    partialX w x y = (y - y₀) * d1 f (u x y) := by
  have hMap : Filter.Tendsto (fun t : ℝ => (t, y)) (nhds x) (nhds (x, y)) :=
    continuousAt_id.prodMk continuousAt_const
  have hCompose' :
      (fun t : ℝ => w t y) =ᶠ[nhds x] (fun t => f (u t y)) :=
    hMap.eventually hCompose
  have hU' :
      (fun t : ℝ => u t y) =ᶠ[nhds x]
        (fun t => (t - x₀) * (y - y₀)) :=
    hMap.eventually hU
  have hUf :
      (fun t : ℝ => f (u t y)) =ᶠ[nhds x]
        (fun t => f ((t - x₀) * (y - y₀))) :=
    hU'.mono (fun _ ht => congrArg f ht)
  have hLocal :
      (fun t : ℝ => w t y) =ᶠ[nhds x]
        (fun t => f ((t - x₀) * (y - y₀))) :=
    hCompose'.trans hUf
  have hUxy : u x y = (x - x₀) * (y - y₀) := hU'.eq_of_nhds
  rw [hUxy] at hDifff ⊢
  have hInner :
      HasDerivAt (fun t : ℝ => (t - x₀) * (y - y₀)) (y - y₀) x := by
    simpa using
      ((hasDerivAt_id x).sub_const x₀).mul
        (hasDerivAt_const x (y - y₀))
  unfold partialX
  calc
    deriv (fun t : ℝ => w t y) x =
        deriv (fun t : ℝ => f ((t - x₀) * (y - y₀))) x :=
      hLocal.deriv_eq
    _ = (y - y₀) * d1 f ((x - x₀) * (y - y₀)) := by
      simpa [d1] using
        (hasDerivAt_comp_local hInner hDifff.hasDerivAt).deriv

theorem gap2 (u w : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (x₀ y₀ x y : ℝ)
    (hWx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX w p.1 p.2 = (p.2 - y₀) * d1 f (u p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = (p.1 - x₀) * (p.2 - y₀))
    (hDiffDf : DifferentiableAt ℝ (deriv f) (u x y)) :
    partialXY w x y = d1 f (u x y) + u x y * d2 f (u x y) := by
  have hMap : Filter.Tendsto (fun t : ℝ => (x, t)) (nhds y) (nhds (x, y)) :=
    continuousAt_const.prodMk continuousAt_id
  have hWx' :
      (fun t : ℝ => partialX w x t) =ᶠ[nhds y]
        (fun t => (t - y₀) * d1 f (u x t)) :=
    hMap.eventually hWx
  have hU' :
      (fun t : ℝ => u x t) =ᶠ[nhds y]
        (fun t => (x - x₀) * (t - y₀)) :=
    hMap.eventually hU
  have hRewrite :
      (fun t : ℝ => (t - y₀) * d1 f (u x t)) =ᶠ[nhds y]
        (fun t => (t - y₀) * d1 f ((x - x₀) * (t - y₀))) :=
    hU'.mono (fun t ht =>
      congrArg (fun z => (t - y₀) * d1 f z) ht)
  have hLocal :
      (fun t : ℝ => partialX w x t) =ᶠ[nhds y]
        (fun t => (t - y₀) * d1 f ((x - x₀) * (t - y₀))) :=
    hWx'.trans hRewrite
  have hUxy : u x y = (x - x₀) * (y - y₀) := hU'.eq_of_nhds
  rw [hUxy] at hDiffDf ⊢
  have hLinear : HasDerivAt (fun t : ℝ => t - y₀) 1 y := by
    simpa using (hasDerivAt_id y).sub_const y₀
  have hInner :
      HasDerivAt (fun t : ℝ => (x - x₀) * (t - y₀)) (x - x₀) y := by
    simpa using (hasDerivAt_const y (x - x₀)).mul hLinear
  unfold partialXY partialY
  calc
    deriv (fun t : ℝ => partialX w x t) y =
        deriv (fun t : ℝ =>
          (t - y₀) * d1 f ((x - x₀) * (t - y₀))) y :=
      hLocal.deriv_eq
    _ = d1 f ((x - x₀) * (y - y₀)) +
        (y - y₀) * (d2 f ((x - x₀) * (y - y₀)) * (x - x₀)) := by
      simpa [d1, d2, mul_comm, mul_left_comm, mul_assoc] using
        (hLinear.mul
          (hasDerivAt_comp_local hInner hDiffDf.hasDerivAt)).deriv
    _ = d1 f ((x - x₀) * (y - y₀)) +
        (x - x₀) * (y - y₀) * d2 f ((x - x₀) * (y - y₀)) := by
      ring

theorem gap3 (u w : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (c x y : ℝ)
    (hMixed : partialXY w x y = d1 f (u x y) + u x y * d2 f (u x y)) :
    partialXY w x y + c * w x y =
      u x y * d2 f (u x y) + d1 f (u x y) + c * w x y := by
  rw [hMixed]
  ring

theorem gap4 (u w : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (c x y : ℝ)
    (hPhysicalPDE : partialXY w x y + c * w x y = 0)
    (hTransform : partialXY w x y + c * w x y =
      u x y * d2 f (u x y) + d1 f (u x y) + c * w x y) :
    u x y * d2 f (u x y) + d1 f (u x y) + c * w x y = 0 := by
  calc
    u x y * d2 f (u x y) + d1 f (u x y) + c * w x y =
        partialXY w x y + c * w x y := hTransform.symm
    _ = 0 := hPhysicalPDE

theorem gap5 (w : ℝ → ℝ → ℝ) (c x y : ℝ)
    (q : ℝ)
    (hTransform : partialXY w x y + c * w x y = q)
    (hZero : q = 0) :
    partialXY w x y + c * w x y = 0 := by
  exact hTransform.trans hZero

end

end ProofGap.Exercise3504
