import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3471_2

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (u v du dv : ℝ) : ℝ :=
  partialX f u v * du + partialY f u v * dv

def physicalDenominator (x y : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  x u v * partialX x u v + y u v * partialY x u v

private theorem coordinateLinesDifferentiableAt (a b : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => (t, b)) a ∧
      DifferentiableAt ℝ (fun t : ℝ => (a, t)) b := by
  constructor
  · have hlin : DifferentiableAt ℝ
        (fun t : ℝ => (ContinuousLinearMap.inl ℝ ℝ ℝ) t) a :=
      (ContinuousLinearMap.inl ℝ ℝ ℝ).differentiableAt
    have hconst : DifferentiableAt ℝ (fun _ : ℝ => ((0 : ℝ), b)) a :=
      differentiableAt_const (x := a) (c := ((0 : ℝ), b))
    simpa using hlin.add hconst
  · have hlin : DifferentiableAt ℝ
        (fun t : ℝ => (ContinuousLinearMap.inr ℝ ℝ ℝ) t) b :=
      (ContinuousLinearMap.inr ℝ ℝ ℝ).differentiableAt
    have hconst : DifferentiableAt ℝ (fun _ : ℝ => (a, (0 : ℝ))) b :=
      differentiableAt_const (x := b) (c := (a, (0 : ℝ)))
    have hshift : DifferentiableAt ℝ
        (fun t : ℝ =>
          (a, (0 : ℝ)) + (ContinuousLinearMap.inr ℝ ℝ ℝ) t) b :=
      hconst.add hlin
    have hfun :
        (fun t : ℝ => (a, t)) =
          (fun t : ℝ =>
            (a, (0 : ℝ)) + (ContinuousLinearMap.inr ℝ ℝ ℝ) t) := by
      funext t
      simp
    rw [hfun]
    exact hshift

theorem gap1 (x z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (u, v))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      p.1 = x p.1 p.2 * z p.1 p.2) :
    du = x u v * differential z u v du dv +
      z u v * differential x u v du dv := by
  rcases coordinateLinesDifferentiableAt u v with ⟨hPairX, hPairY⟩
  have hxX : DifferentiableAt ℝ (fun t : ℝ => x t v) u := by
    simpa [Function.comp_def, Function.uncurry] using hxDiff.comp u hPairX
  have hzX : DifferentiableAt ℝ (fun t : ℝ => z t v) u := by
    simpa [Function.comp_def, Function.uncurry] using hzDiff.comp u hPairX
  have hxY : DifferentiableAt ℝ (fun t : ℝ => x u t) v := by
    simpa [Function.comp_def, Function.uncurry] using hxDiff.comp v hPairY
  have hzY : DifferentiableAt ℝ (fun t : ℝ => z u t) v := by
    simpa [Function.comp_def, Function.uncurry] using hzDiff.comp v hPairY
  have hxXDeriv : HasDerivAt (fun t : ℝ => x t v) (partialX x u v) u := by
    simpa [partialX] using hxX.hasDerivAt
  have hzXDeriv : HasDerivAt (fun t : ℝ => z t v) (partialX z u v) u := by
    simpa [partialX] using hzX.hasDerivAt
  have hxYDeriv : HasDerivAt (fun t : ℝ => x u t) (partialY x u v) v := by
    simpa [partialY] using hxY.hasDerivAt
  have hzYDeriv : HasDerivAt (fun t : ℝ => z u t) (partialY z u v) v := by
    simpa [partialY] using hzY.hasDerivAt
  have hUx : ∀ᶠ t : ℝ in nhds u, t = x t v * z t v := by
    simpa using hPairX.continuousAt.eventually hU
  have hUy : ∀ᶠ t : ℝ in nhds v, u = x u t * z u t := by
    simpa using hPairY.continuousAt.eventually hU
  have hDerivX :
      1 = partialX x u v * z u v + x u v * partialX z u v := by
    calc
      1 = deriv (fun t : ℝ => t) u := (hasDerivAt_id u).deriv.symm
      _ = deriv (fun t : ℝ => x t v * z t v) u :=
        Filter.EventuallyEq.deriv_eq hUx
      _ = partialX x u v * z u v + x u v * partialX z u v :=
        (hxXDeriv.mul hzXDeriv).deriv
  have hDerivY :
      0 = partialY x u v * z u v + x u v * partialY z u v := by
    calc
      0 = deriv (fun _ : ℝ => u) v :=
        (hasDerivAt_const (x := v) (c := u)).deriv.symm
      _ = deriv (fun t : ℝ => x u t * z u t) v :=
        Filter.EventuallyEq.deriv_eq hUy
      _ = partialY x u v * z u v + x u v * partialY z u v :=
        (hxYDeriv.mul hzYDeriv).deriv
  unfold differential
  linear_combination du * hDerivX + dv * hDerivY

theorem gap2 (y z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (u, v))
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (u, v),
      p.2 = y p.1 p.2 * z p.1 p.2) :
    dv = y u v * differential z u v du dv +
      z u v * differential y u v du dv := by
  rcases coordinateLinesDifferentiableAt u v with ⟨hPairX, hPairY⟩
  have hyX : DifferentiableAt ℝ (fun t : ℝ => y t v) u := by
    simpa [Function.comp_def, Function.uncurry] using hyDiff.comp u hPairX
  have hzX : DifferentiableAt ℝ (fun t : ℝ => z t v) u := by
    simpa [Function.comp_def, Function.uncurry] using hzDiff.comp u hPairX
  have hyY : DifferentiableAt ℝ (fun t : ℝ => y u t) v := by
    simpa [Function.comp_def, Function.uncurry] using hyDiff.comp v hPairY
  have hzY : DifferentiableAt ℝ (fun t : ℝ => z u t) v := by
    simpa [Function.comp_def, Function.uncurry] using hzDiff.comp v hPairY
  have hyXDeriv : HasDerivAt (fun t : ℝ => y t v) (partialX y u v) u := by
    simpa [partialX] using hyX.hasDerivAt
  have hzXDeriv : HasDerivAt (fun t : ℝ => z t v) (partialX z u v) u := by
    simpa [partialX] using hzX.hasDerivAt
  have hyYDeriv : HasDerivAt (fun t : ℝ => y u t) (partialY y u v) v := by
    simpa [partialY] using hyY.hasDerivAt
  have hzYDeriv : HasDerivAt (fun t : ℝ => z u t) (partialY z u v) v := by
    simpa [partialY] using hzY.hasDerivAt
  have hVx : ∀ᶠ t : ℝ in nhds u, v = y t v * z t v := by
    simpa using hPairX.continuousAt.eventually hV
  have hVy : ∀ᶠ t : ℝ in nhds v, t = y u t * z u t := by
    simpa using hPairY.continuousAt.eventually hV
  have hDerivX :
      0 = partialX y u v * z u v + y u v * partialX z u v := by
    calc
      0 = deriv (fun _ : ℝ => v) u :=
        (hasDerivAt_const (x := u) (c := v)).deriv.symm
      _ = deriv (fun t : ℝ => y t v * z t v) u :=
        Filter.EventuallyEq.deriv_eq hVx
      _ = partialX y u v * z u v + y u v * partialX z u v :=
        (hyXDeriv.mul hzXDeriv).deriv
  have hDerivY :
      1 = partialY y u v * z u v + y u v * partialY z u v := by
    calc
      1 = deriv (fun t : ℝ => t) v := (hasDerivAt_id v).deriv.symm
      _ = deriv (fun t : ℝ => y u t * z u t) v :=
        Filter.EventuallyEq.deriv_eq hVy
      _ = partialY y u v * z u v + y u v * partialY z u v :=
        (hyYDeriv.mul hzYDeriv).deriv
  unfold differential
  linear_combination du * hDerivX + dv * hDerivY

theorem gap3 (x : ℝ → ℝ → ℝ) (u v du dv : ℝ) :
    differential x u v du dv =
      partialX x u v * du + partialY x u v * dv := by
  rfl

theorem gap4 (x y z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hDu : du = x u v * differential z u v du dv +
      z u v * differential x u v du dv)
    (hDv : dv = y u v * differential z u v du dv +
      z u v * differential y u v du dv) :
    partialX x u v * du + partialY x u v * dv =
      partialX x u v *
          (x u v * differential z u v du dv +
            z u v * differential x u v du dv) +
        partialY x u v *
          (y u v * differential z u v du dv +
            z u v * differential y u v du dv) := by
  exact congrArg₂
    (fun a b : ℝ => partialX x u v * a + partialY x u v * b)
    hDu hDv

theorem gap5 (x y z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hDx : differential x u v du dv =
      partialX x u v * du + partialY x u v * dv)
    (hSubstitution :
      partialX x u v * du + partialY x u v * dv =
        partialX x u v *
            (x u v * differential z u v du dv +
              z u v * differential x u v du dv) +
          partialY x u v *
            (y u v * differential z u v du dv +
              z u v * differential y u v du dv)) :
    differential x u v du dv =
      partialX x u v *
          (x u v * differential z u v du dv +
            z u v * differential x u v du dv) +
        partialY x u v *
          (y u v * differential z u v du dv +
            z u v * differential y u v du dv) := by
  exact hDx.trans hSubstitution

theorem gap6 (x y z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hExpanded :
      differential x u v du dv =
        partialX x u v *
            (x u v * differential z u v du dv +
              z u v * differential x u v du dv) +
          partialY x u v *
            (y u v * differential z u v du dv +
              z u v * differential y u v du dv)) :
    physicalDenominator x y u v * differential z u v du dv =
      (1 - z u v * partialX x u v) * differential x u v du dv -
        z u v * partialY x u v * differential y u v du dv := by
  unfold physicalDenominator
  linear_combination -1 * hExpanded

theorem gap7 (x y z Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : physicalDenominator x y u v ≠ 0)
    (hForm : ∀ dx dy,
      physicalDenominator x y u v *
          differential Z (x u v) (y u v) dx dy =
        (1 - z u v * partialX x u v) * dx -
          z u v * partialY x u v * dy) :
    partialX Z (x u v) (y u v) =
      (1 - z u v * partialX x u v) / physicalDenominator x y u v := by
  apply (eq_div_iff hDen).2
  have h := hForm 1 0
  simpa [differential, mul_comm] using h

theorem gap8 (x y z Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hDen : physicalDenominator x y u v ≠ 0)
    (hForm : ∀ dx dy,
      physicalDenominator x y u v *
          differential Z (x u v) (y u v) dx dy =
        (1 - z u v * partialX x u v) * dx -
          z u v * partialY x u v * dy) :
    partialY Z (x u v) (y u v) =
      -(z u v * partialY x u v) / physicalDenominator x y u v := by
  apply (eq_div_iff hDen).2
  have h := hForm 0 1
  simpa [differential, mul_comm] using h

theorem gap9 (A x y z Z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hA : A u v =
      partialX Z (x u v) (y u v) ^ 2 +
        partialY Z (x u v) (y u v) ^ 2)
    (hZx : partialX Z (x u v) (y u v) =
      (1 - z u v * partialX x u v) / physicalDenominator x y u v)
    (hZy : partialY Z (x u v) (y u v) =
      -(z u v * partialY x u v) / physicalDenominator x y u v) :
    A u v =
      ((1 - z u v * partialX x u v) ^ 2 +
        z u v ^ 2 * partialY x u v ^ 2) /
          physicalDenominator x y u v ^ 2 := by
  rw [hA, hZx, hZy]
  ring

theorem gap10 (x y z : ℝ → ℝ → ℝ) (u v : ℝ) :
    ((1 - z u v * partialX x u v) ^ 2 +
        z u v ^ 2 * partialY x u v ^ 2) /
          physicalDenominator x y u v ^ 2 =
      (1 - 2 * z u v * partialX x u v +
        z u v ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2)) /
          physicalDenominator x y u v ^ 2 := by
  ring

theorem gap11 (A x y z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hA : A u v =
      ((1 - z u v * partialX x u v) ^ 2 +
        z u v ^ 2 * partialY x u v ^ 2) /
          physicalDenominator x y u v ^ 2)
    (hExpand :
      ((1 - z u v * partialX x u v) ^ 2 +
          z u v ^ 2 * partialY x u v ^ 2) /
            physicalDenominator x y u v ^ 2 =
        (1 - 2 * z u v * partialX x u v +
          z u v ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2)) /
            physicalDenominator x y u v ^ 2) :
    A u v =
      (1 - 2 * z u v * partialX x u v +
        z u v ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2)) /
          physicalDenominator x y u v ^ 2 := by
  exact hA.trans hExpand

theorem gap12 (A x y z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hx : x u v ≠ 0) (hu : u ≠ 0)
    (hU : u = x u v * z u v)
    (hV : v = y u v * z u v)
    (hA : A u v =
      (1 - 2 * z u v * partialX x u v +
        z u v ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2)) /
          physicalDenominator x y u v ^ 2) :
    A u v =
      u ^ 2 *
          (x u v ^ 2 - 2 * x u v * u * partialX x u v +
            u ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2)) /
        (x u v ^ 4 *
          (u * partialX x u v + v * partialY x u v) ^ 2) := by
  have hB :
      u * partialX x u v + v * partialY x u v =
        z u v * physicalDenominator x y u v := by
    unfold physicalDenominator
    linear_combination
      partialX x u v * hU + partialY x u v * hV
  have hUSq :
      u ^ 2 = x u v ^ 2 * z u v ^ 2 := by
    calc
      u ^ 2 = (x u v * z u v) ^ 2 :=
        congrArg (fun t : ℝ => t ^ 2) hU
      _ = x u v ^ 2 * z u v ^ 2 := by ring
  have hQ :
      x u v ^ 2 - 2 * x u v * u * partialX x u v +
          u ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2) =
        x u v ^ 2 *
          (1 - 2 * z u v * partialX x u v +
            z u v ^ 2 *
              (partialX x u v ^ 2 + partialY x u v ^ 2)) := by
    linear_combination
      (-2 * x u v * partialX x u v) * hU +
        (partialX x u v ^ 2 + partialY x u v ^ 2) * hUSq
  have hBSq :
      (u * partialX x u v + v * partialY x u v) ^ 2 =
        (z u v * physicalDenominator x y u v) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hB
  have hScaleEq :
      (u * x u v) ^ 2 = x u v ^ 4 * z u v ^ 2 := by
    calc
      (u * x u v) ^ 2 = u ^ 2 * x u v ^ 2 := by ring
      _ = (x u v ^ 2 * z u v ^ 2) * x u v ^ 2 := by rw [hUSq]
      _ = x u v ^ 4 * z u v ^ 2 := by ring
  have hNumScale :
      u ^ 2 *
          (x u v ^ 2 - 2 * x u v * u * partialX x u v +
            u ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2)) =
        (u * x u v) ^ 2 *
          (1 - 2 * z u v * partialX x u v +
            z u v ^ 2 *
              (partialX x u v ^ 2 + partialY x u v ^ 2)) := by
    rw [hQ]
    ring
  have hDenScale :
      x u v ^ 4 *
          (u * partialX x u v + v * partialY x u v) ^ 2 =
        (u * x u v) ^ 2 * physicalDenominator x y u v ^ 2 := by
    calc
      x u v ^ 4 *
          (u * partialX x u v + v * partialY x u v) ^ 2 =
        x u v ^ 4 *
          (z u v * physicalDenominator x y u v) ^ 2 := by rw [hBSq]
      _ = (u * x u v) ^ 2 * physicalDenominator x y u v ^ 2 := by
        rw [hScaleEq]
        ring
  have hScale : (u * x u v) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hu hx)
  have hFrac :
      (1 - 2 * z u v * partialX x u v +
          z u v ^ 2 *
            (partialX x u v ^ 2 + partialY x u v ^ 2)) /
          physicalDenominator x y u v ^ 2 =
        ((u * x u v) ^ 2 *
            (1 - 2 * z u v * partialX x u v +
              z u v ^ 2 *
                (partialX x u v ^ 2 + partialY x u v ^ 2))) /
          ((u * x u v) ^ 2 * physicalDenominator x y u v ^ 2) := by
    by_cases hDen : physicalDenominator x y u v = 0
    · simp [hDen]
    · field_simp [hDen, hScale]
  calc
    A u v =
        (1 - 2 * z u v * partialX x u v +
          z u v ^ 2 *
            (partialX x u v ^ 2 + partialY x u v ^ 2)) /
          physicalDenominator x y u v ^ 2 := hA
    _ =
        ((u * x u v) ^ 2 *
            (1 - 2 * z u v * partialX x u v +
              z u v ^ 2 *
                (partialX x u v ^ 2 + partialY x u v ^ 2))) /
          ((u * x u v) ^ 2 * physicalDenominator x y u v ^ 2) := hFrac
    _ =
        u ^ 2 *
            (x u v ^ 2 - 2 * x u v * u * partialX x u v +
              u ^ 2 * (partialX x u v ^ 2 + partialY x u v ^ 2)) /
          (x u v ^ 4 *
            (u * partialX x u v + v * partialY x u v) ^ 2) := by
      rw [hNumScale, hDenScale]

end

end ProofGap.Exercise3471_2
