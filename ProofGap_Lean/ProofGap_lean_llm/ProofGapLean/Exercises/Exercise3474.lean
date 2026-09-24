import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace ProofGap.Exercise3474

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (u v du dv : ℝ) : ℝ :=
  partialX f u v * du + partialY f u v * dv

private lemma partialX_eq_fderiv3474
    {f : ℝ → ℝ → ℝ} {u v : ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (u, v)) :
    partialX f u v =
      fderiv ℝ (Function.uncurry f) (u, v) (1, 0) := by
  have hline :
      HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
  have hc := hf.hasFDerivAt.comp_hasDerivAt u hline
  unfold partialX
  simpa [Function.comp_apply, Function.uncurry] using hc.deriv

private lemma partialY_eq_fderiv3474
    {f : ℝ → ℝ → ℝ} {u v : ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (u, v)) :
    partialY f u v =
      fderiv ℝ (Function.uncurry f) (u, v) (0, 1) := by
  have hline :
      HasDerivAt (fun s : ℝ => (u, s)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id v)
  have hc := hf.hasFDerivAt.comp_hasDerivAt v hline
  unfold partialY
  simpa [Function.comp_apply, Function.uncurry] using hc.deriv

private lemma differential_eq_fderiv3474
    {f : ℝ → ℝ → ℝ} {u v du dv : ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (u, v)) :
    differential f u v du dv =
      fderiv ℝ (Function.uncurry f) (u, v) (du, dv) := by
  let L := fderiv ℝ (Function.uncurry f) (u, v)
  have hvec :
      ((du, dv) : ℝ × ℝ) =
        du • ((1, 0) : ℝ × ℝ) + dv • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [differential, partialX_eq_fderiv3474 hf,
    partialY_eq_fderiv3474 hf, show
      fderiv ℝ (Function.uncurry f) (u, v) (du, dv) =
        L (du, dv) by rfl, hvec, map_add, map_smul, map_smul]
  dsimp [L]
  ring

theorem gap1 (x y : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hCoord : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      p.1 = x p.1 p.2 ^ 2 + y p.1 p.2 ^ 2) :
    du =
      2 * x u v * differential x u v du dv +
        2 * y u v * differential y u v du dv := by
  have hleft :
      HasFDerivAt (fun p : ℝ × ℝ => p.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (u, v) :=
    hasFDerivAt_fst
  have hright :=
    (hxDiff.hasFDerivAt.pow 2).add (hyDiff.hasFDerivAt.pow 2)
  have heq :
      (fun p : ℝ × ℝ => p.1) =ᶠ[nhds (u, v)]
        (fun p => x p.1 p.2 ^ 2 + y p.1 p.2 ^ 2) := hCoord
  have heqF := heq.fderiv_eq (𝕜 := ℝ)
  have hrightF :
      fderiv ℝ (fun p : ℝ × ℝ =>
        x p.1 p.2 ^ 2 + y p.1 p.2 ^ 2) (u, v) =
        (2 • x u v) • fderiv ℝ (Function.uncurry x) (u, v) +
          (2 • y u v) • fderiv ℝ (Function.uncurry y) (u, v) := by
    simpa [Function.uncurry] using hright.fderiv
  rw [hleft.fderiv, hrightF] at heqF
  have happ := congrArg
    (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (du, dv)) heqF
  simp at happ
  rw [← differential_eq_fderiv3474 hxDiff,
    ← differential_eq_fderiv3474 hyDiff] at happ
  simpa [Function.uncurry, mul_comm, mul_left_comm, mul_assoc] using happ

theorem gap2 (x y : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hx : x u v ≠ 0) (hy : y u v ≠ 0)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hCoord : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      p.2 = 1 / x p.1 p.2 + 1 / y p.1 p.2) :
    dv =
      -(1 / x u v ^ 2) * differential x u v du dv -
        (1 / y u v ^ 2) * differential y u v du dv := by
  have hleft :
      HasFDerivAt (fun p : ℝ × ℝ => p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) :=
    hasFDerivAt_snd
  have hxInv :=
    (hasFDerivAt_inv hx).comp (u, v) hxDiff.hasFDerivAt
  have hyInv :=
    (hasFDerivAt_inv hy).comp (u, v) hyDiff.hasFDerivAt
  have hright :
      HasFDerivAt (𝕜 := ℝ) (fun p : ℝ × ℝ =>
        1 / x p.1 p.2 + 1 / y p.1 p.2)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(x u v ^ 2)⁻¹)).comp
            (fderiv ℝ (Function.uncurry x) (u, v)) +
          (ContinuousLinearMap.toSpanSingleton ℝ (-(y u v ^ 2)⁻¹)).comp
            (fderiv ℝ (Function.uncurry y) (u, v))) (u, v) := by
    simpa [Function.comp_def, Function.uncurry, one_div] using hxInv.add hyInv
  have heq :
      (fun p : ℝ × ℝ => p.2) =ᶠ[nhds (u, v)]
        (fun p => 1 / x p.1 p.2 + 1 / y p.1 p.2) := hCoord
  have heqF := heq.fderiv_eq (𝕜 := ℝ)
  rw [hleft.fderiv, hright.fderiv] at heqF
  have happ := congrArg
    (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (du, dv)) heqF
  simp [Function.comp_apply] at happ
  rw [← differential_eq_fderiv3474 hxDiff,
    ← differential_eq_fderiv3474 hyDiff] at happ
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using happ

theorem gap3 (x y z w : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hzPos : 0 < z u v)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (u, v))
    (hwDiff : DifferentiableAt ℝ (Function.uncurry w) (u, v))
    (hW : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      w p.1 p.2 = Real.log (z p.1 p.2) - (x p.1 p.2 + y p.1 p.2)) :
    differential w u v du dv =
      (1 / z u v) * differential z u v du dv -
        differential x u v du dv - differential y u v du dv := by
  have hleft := hwDiff.hasFDerivAt
  have hright :
      HasFDerivAt (𝕜 := ℝ) (fun p : ℝ × ℝ =>
        Real.log (z p.1 p.2) - (x p.1 p.2 + y p.1 p.2))
        ((z u v)⁻¹ • fderiv ℝ (Function.uncurry z) (u, v) -
          (fderiv ℝ (Function.uncurry x) (u, v) +
            fderiv ℝ (Function.uncurry y) (u, v))) (u, v) := by
    simpa [Function.uncurry] using
      (hzDiff.hasFDerivAt.log hzPos.ne').sub
        (hxDiff.hasFDerivAt.add hyDiff.hasFDerivAt)
  have heq :
      Function.uncurry w =ᶠ[nhds (u, v)]
        (fun p : ℝ × ℝ =>
          Real.log (z p.1 p.2) - (x p.1 p.2 + y p.1 p.2)) := by
    simpa [Function.uncurry] using hW
  have heqF := heq.fderiv_eq (𝕜 := ℝ)
  rw [hleft.fderiv, hright.fderiv] at heqF
  have happ := congrArg
    (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (du, dv)) heqF
  simp at happ
  rw [← differential_eq_fderiv3474 hwDiff,
    ← differential_eq_fderiv3474 hzDiff,
    ← differential_eq_fderiv3474 hxDiff,
    ← differential_eq_fderiv3474 hyDiff] at happ
  simpa [one_div, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using happ

theorem gap4 (w : ℝ → ℝ → ℝ) (u v du dv : ℝ) :
    differential w u v du dv =
      partialX w u v * du + partialY w u v * dv := by
  rfl

theorem gap5 (x y z w Z : ℝ → ℝ → ℝ) (u v dx dy : ℝ)
    (hLog :
      differential w u v
          (2 * x u v * dx + 2 * y u v * dy)
          (-(1 / x u v ^ 2) * dx - (1 / y u v ^ 2) * dy) =
        (1 / z u v) * differential Z (x u v) (y u v) dx dy - dx - dy)
    (hTotal :
      differential w u v
          (2 * x u v * dx + 2 * y u v * dy)
          (-(1 / x u v ^ 2) * dx - (1 / y u v ^ 2) * dy) =
        partialX w u v * (2 * x u v * dx + 2 * y u v * dy) +
          partialY w u v *
            (-(1 / x u v ^ 2) * dx - (1 / y u v ^ 2) * dy)) :
    (1 / z u v) * differential Z (x u v) (y u v) dx dy - dx - dy =
      partialX w u v * (2 * x u v * dx + 2 * y u v * dy) +
        partialY w u v *
          (-(1 / x u v ^ 2) * dx - (1 / y u v ^ 2) * dy) := by
  rw [← hTotal]
  exact hLog.symm

theorem gap6 (x y z w Z : ℝ → ℝ → ℝ) (u v dx dy : ℝ)
    (hz : z u v ≠ 0)
    (hEquation :
      (1 / z u v) * differential Z (x u v) (y u v) dx dy - dx - dy =
        partialX w u v * (2 * x u v * dx + 2 * y u v * dy) +
          partialY w u v *
            (-(1 / x u v ^ 2) * dx - (1 / y u v ^ 2) * dy)) :
    differential Z (x u v) (y u v) dx dy =
      (2 * x u v * z u v * partialX w u v -
          z u v / x u v ^ 2 * partialY w u v + z u v) * dx +
        (2 * y u v * z u v * partialX w u v -
          z u v / y u v ^ 2 * partialY w u v + z u v) * dy := by
  have hsolve :
      (1 / z u v) * differential Z (x u v) (y u v) dx dy =
        partialX w u v * (2 * x u v * dx + 2 * y u v * dy) +
          partialY w u v *
            (-(1 / x u v ^ 2) * dx - (1 / y u v ^ 2) * dy) +
          dx + dy := by
    linarith [hEquation]
  calc
    differential Z (x u v) (y u v) dx dy =
        z u v *
          ((1 / z u v) * differential Z (x u v) (y u v) dx dy) := by
            field_simp [hz]
    _ = z u v *
        (partialX w u v * (2 * x u v * dx + 2 * y u v * dy) +
          partialY w u v *
            (-(1 / x u v ^ 2) * dx - (1 / y u v ^ 2) * dy) +
          dx + dy) := by rw [hsolve]
    _ = (2 * x u v * z u v * partialX w u v -
          z u v / x u v ^ 2 * partialY w u v + z u v) * dx +
        (2 * y u v * z u v * partialX w u v -
          z u v / y u v ^ 2 * partialY w u v + z u v) * dy := by
            ring

theorem gap7 (x y z w Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hPDE :
      y u v * partialX Z (x u v) (y u v) -
        x u v * partialY Z (x u v) (y u v) =
          (y u v - x u v) * z u v)
    (hZx : partialX Z (x u v) (y u v) =
      2 * x u v * z u v * partialX w u v -
        z u v / x u v ^ 2 * partialY w u v + z u v)
    (hZy : partialY Z (x u v) (y u v) =
      2 * y u v * z u v * partialX w u v -
        z u v / y u v ^ 2 * partialY w u v + z u v) :
    y u v * z u v *
          (2 * x u v * partialX w u v -
            1 / x u v ^ 2 * partialY w u v + 1) -
        x u v * z u v *
          (2 * y u v * partialX w u v -
            1 / y u v ^ 2 * partialY w u v + 1) =
      (y u v - x u v) * z u v := by
  rw [hZx, hZy] at hPDE
  ring_nf at hPDE ⊢
  exact hPDE

theorem gap8 (x y z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hz : z u v ≠ 0)
    (hCoefficient : x u v / y u v ^ 2 - y u v / x u v ^ 2 ≠ 0)
    (hEquation :
      y u v * z u v *
            (2 * x u v * partialX w u v -
              1 / x u v ^ 2 * partialY w u v + 1) -
          x u v * z u v *
            (2 * y u v * partialX w u v -
              1 / y u v ^ 2 * partialY w u v + 1) =
        (y u v - x u v) * z u v) :
    partialY w u v = 0 := by
  have hzero :
      (z u v *
          (x u v / y u v ^ 2 - y u v / x u v ^ 2)) *
        partialY w u v = 0 := by
    linear_combination hEquation
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hz hCoefficient)

end

end ProofGap.Exercise3474
