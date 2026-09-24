import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3464

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def radial (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2 + z x y ^ 2)

def transformedDenominator (Z : ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  1 - partialY Z (u x y) (v x y) -
    z x y / radial z x y * partialY Z (u x y) (v x y)

private theorem differential_eq_fderiv (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    differential f x y dx dy =
      fderiv ℝ (Function.uncurry f) (x, y) (dx, dy) := by
  have hxFD := hf.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) y x))
  have hyFD := hf.hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) x y).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) y))
  have hpx : partialX f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (1, 0) := by
    unfold partialX deriv
    have hxEval :=
      congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hxFD.fderiv
    simpa [Function.comp_def, Function.uncurry, id_eq] using hxEval
  have hpy : partialY f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (0, 1) := by
    unfold partialY deriv
    have hyEval :=
      congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hyFD.fderiv
    simpa [Function.comp_def, Function.uncurry, id_eq] using hyEval
  rw [differential, hpx, hpy]
  have hp : (dx, dy) =
      dx • ((1 : ℝ), (0 : ℝ)) + dy • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hp, map_add, map_smul, map_smul]
  simp [smul_eq_mul, mul_comm]

theorem gap1 (u : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hx : x ≠ 0)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.2 / p.1) :
    differential u x y dx dy = (x * dy - y * dx) / x ^ 2 := by
  have hlineX :=
    (hasFDerivAt_id (𝕜 := ℝ) x).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) y x)
  have hlineY :=
    (hasFDerivAt_const (𝕜 := ℝ) x y).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) y)
  have hUx : ∀ᶠ t : ℝ in nhds x, u t y = y / t := by
    simpa [id_eq] using hlineX.continuousAt.eventually hU
  have hUy : ∀ᶠ t : ℝ in nhds y, u x t = t / x := by
    simpa [id_eq] using hlineY.continuousAt.eventually hU
  have hdx : HasDerivAt (fun t : ℝ => y / t) (-y / x ^ 2) x := by
    simpa [id_eq] using
      (hasDerivAt_const x y).div (hasDerivAt_id x) hx
  have hdy : HasDerivAt (fun t : ℝ => t / x) (1 / x) y := by
    convert (hasDerivAt_id y).div (hasDerivAt_const y x) hx using 1 <;>
      simp [id_eq] <;>
      field_simp [hx] <;>
      ring
  have huX : partialX u x y = -y / x ^ 2 := by
    unfold partialX
    exact (hdx.congr_of_eventuallyEq hUx).deriv
  have huY : partialY u x y = 1 / x := by
    unfold partialY
    exact (hdy.congr_of_eventuallyEq hUy).deriv
  rw [differential, huX, huY]
  field_simp [hx] <;> ring

theorem gap2 (z v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hr : radial z x y ≠ 0)
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = z p.1 p.2 + radial z p.1 p.2) :
    differential v x y dx dy =
      differential z x y dx dy +
        (x * dx + y * dy + z x y * differential z x y dx dy) /
          radial z x y := by
  have hlineX :=
    (hasFDerivAt_id (𝕜 := ℝ) x).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) y x)
  have hlineY :=
    (hasFDerivAt_const (𝕜 := ℝ) x y).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) y)
  have hzXDiff : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    simpa [Function.uncurry, id_eq] using
      (hzDiff.hasFDerivAt.comp x hlineX).differentiableAt
  have hzYDiff : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    simpa [Function.uncurry, id_eq] using
      (hzDiff.hasFDerivAt.comp y hlineY).differentiableAt
  have hzX : HasDerivAt (fun t : ℝ => z t y) (partialX z x y) x := by
    simpa [partialX] using hzXDiff.hasDerivAt
  have hzY : HasDerivAt (fun t : ℝ => z x t) (partialY z x y) y := by
    simpa [partialY] using hzYDiff.hasDerivAt
  have hqX : HasDerivAt
      (fun t : ℝ => t ^ 2 + y ^ 2 + z t y ^ 2)
      (2 * x + 2 * z x y * partialX z x y) x := by
    convert ((((hasDerivAt_id x).pow 2).add
      (hasDerivAt_const x (y ^ 2))).add (hzX.pow 2)) using 1 <;>
      simp [id_eq] <;> ring
  have hqY : HasDerivAt
      (fun t : ℝ => x ^ 2 + t ^ 2 + z x t ^ 2)
      (2 * y + 2 * z x y * partialY z x y) y := by
    convert (((hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).pow 2)).add (hzY.pow 2)) using 1 <;>
      simp [id_eq] <;> ring
  have hqne : x ^ 2 + y ^ 2 + z x y ^ 2 ≠ 0 := by
    intro h
    apply hr
    simp [radial, h]
  have hradXRaw : HasDerivAt (fun t : ℝ => radial z t y)
      (1 / (2 * radial z x y) *
        (2 * x + 2 * z x y * partialX z x y)) x := by
    simpa [radial, Function.comp_def] using
      (Real.hasDerivAt_sqrt hqne).comp x hqX
  have hradYRaw : HasDerivAt (fun t : ℝ => radial z x t)
      (1 / (2 * radial z x y) *
        (2 * y + 2 * z x y * partialY z x y)) y := by
    simpa [radial, Function.comp_def] using
      (Real.hasDerivAt_sqrt hqne).comp y hqY
  have hradX : HasDerivAt (fun t : ℝ => radial z t y)
      ((x + z x y * partialX z x y) / radial z x y) x := by
    apply hradXRaw.congr_deriv
    field_simp [hr] <;> ring
  have hradY : HasDerivAt (fun t : ℝ => radial z x t)
      ((y + z x y * partialY z x y) / radial z x y) y := by
    apply hradYRaw.congr_deriv
    field_simp [hr] <;> ring
  have hVx : ∀ᶠ t : ℝ in nhds x,
      v t y = z t y + radial z t y := by
    simpa [id_eq] using hlineX.continuousAt.eventually hV
  have hVy : ∀ᶠ t : ℝ in nhds y,
      v x t = z x t + radial z x t := by
    simpa [id_eq] using hlineY.continuousAt.eventually hV
  have hvX : partialX v x y = partialX z x y +
      (x + z x y * partialX z x y) / radial z x y := by
    unfold partialX
    exact ((hzX.add hradX).congr_of_eventuallyEq hVx).deriv
  have hvY : partialY v x y = partialY z x y +
      (y + z x y * partialY z x y) / radial z x y := by
    unfold partialY
    exact ((hzY.add hradY).congr_of_eventuallyEq hVy).deriv
  rw [differential, hvX, hvY]
  unfold differential
  field_simp [hr] <;> ring

theorem gap3 (u v z Z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hZDiff : DifferentiableAt ℝ (Function.uncurry Z) (u x y, v x y))
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = Z (u p.1 p.2) (v p.1 p.2)) :
    differential z x y dx dy =
      partialX Z (u x y) (v x y) * differential u x y dx dy +
        partialY Z (u x y) (v x y) * differential v x y dx dy := by
  have hCompEq :
      Function.uncurry z =ᶠ[nhds (x, y)]
        (Function.uncurry Z ∘ fun p : ℝ × ℝ =>
          (Function.uncurry u p, Function.uncurry v p)) := by
    simpa [Function.comp_def, Function.uncurry] using hCompose
  have hCompFD := hZDiff.hasFDerivAt.comp (x, y)
    (huDiff.hasFDerivAt.prodMk hvDiff.hasFDerivAt)
  have hzFD := hCompFD.congr_of_eventuallyEq hCompEq
  rw [differential_eq_fderiv z x y dx dy hzDiff]
  rw [hzFD.fderiv]
  change
    fderiv ℝ (Function.uncurry Z) (u x y, v x y)
        (fderiv ℝ (Function.uncurry u) (x, y) (dx, dy),
          fderiv ℝ (Function.uncurry v) (x, y) (dx, dy)) = _
  rw [← differential_eq_fderiv u x y dx dy huDiff]
  rw [← differential_eq_fderiv v x y dx dy hvDiff]
  exact (differential_eq_fderiv Z (u x y) (v x y)
    (differential u x y dx dy) (differential v x y dx dy) hZDiff).symm

theorem gap4 (u v z Z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hChain :
      differential z x y dx dy =
        partialX Z (u x y) (v x y) * differential u x y dx dy +
          partialY Z (u x y) (v x y) * differential v x y dx dy)
    (hDu : differential u x y dx dy = dy / x - y * dx / x ^ 2)
    (hDv : differential v x y dx dy =
      differential z x y dx dy +
        x / radial z x y * dx + y / radial z x y * dy +
          z x y / radial z x y * differential z x y dx dy) :
    differential z x y dx dy =
      partialX Z (u x y) (v x y) * (dy / x - y * dx / x ^ 2) +
        partialY Z (u x y) (v x y) *
          (differential z x y dx dy +
            x / radial z x y * dx + y / radial z x y * dy +
              z x y / radial z x y * differential z x y dx dy) := by
  simpa only [hDu, hDv] using hChain

theorem gap5 (u v z Z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hExpanded :
      differential z x y dx dy =
        partialX Z (u x y) (v x y) * (dy / x - y * dx / x ^ 2) +
          partialY Z (u x y) (v x y) *
            (differential z x y dx dy +
              x / radial z x y * dx + y / radial z x y * dy +
                z x y / radial z x y * differential z x y dx dy)) :
    transformedDenominator Z z u v x y * differential z x y dx dy =
      (-y / x ^ 2 * partialX Z (u x y) (v x y) +
          x / radial z x y * partialY Z (u x y) (v x y)) * dx +
        (1 / x * partialX Z (u x y) (v x y) +
          y / radial z x y * partialY Z (u x y) (v x y)) * dy := by
  unfold transformedDenominator
  linear_combination hExpanded

theorem gap6 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : transformedDenominator Z z u v x y ≠ 0)
    (hForm : ∀ dx dy,
      transformedDenominator Z z u v x y * differential z x y dx dy =
        (-y / x ^ 2 * partialX Z (u x y) (v x y) +
            x / radial z x y * partialY Z (u x y) (v x y)) * dx +
          (1 / x * partialX Z (u x y) (v x y) +
            y / radial z x y * partialY Z (u x y) (v x y)) * dy) :
    partialX z x y =
      (-y / x ^ 2 * partialX Z (u x y) (v x y) +
          x / radial z x y * partialY Z (u x y) (v x y)) /
        transformedDenominator Z z u v x y := by
  have h := hForm 1 0
  simp [differential] at h
  apply (eq_div_iff hDen).2
  simpa [mul_comm] using h

theorem gap7 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : transformedDenominator Z z u v x y ≠ 0)
    (hForm : ∀ dx dy,
      transformedDenominator Z z u v x y * differential z x y dx dy =
        (-y / x ^ 2 * partialX Z (u x y) (v x y) +
            x / radial z x y * partialY Z (u x y) (v x y)) * dx +
          (1 / x * partialX Z (u x y) (v x y) +
            y / radial z x y * partialY Z (u x y) (v x y)) * dy) :
    partialY z x y =
      (1 / x * partialX Z (u x y) (v x y) +
          y / radial z x y * partialY Z (u x y) (v x y)) /
        transformedDenominator Z z u v x y := by
  have h := hForm 0 1
  simp [differential] at h
  apply (eq_div_iff hDen).2
  simpa [mul_comm] using h

theorem gap8 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : transformedDenominator Z z u v x y ≠ 0)
    (hPDE : x * partialX z x y + y * partialY z x y =
      z x y + radial z x y)
    (hZx : partialX z x y =
      (-y / x ^ 2 * partialX Z (u x y) (v x y) +
          x / radial z x y * partialY Z (u x y) (v x y)) /
        transformedDenominator Z z u v x y)
    (hZy : partialY z x y =
      (1 / x * partialX Z (u x y) (v x y) +
          y / radial z x y * partialY Z (u x y) (v x y)) /
        transformedDenominator Z z u v x y) :
    x * (-y / x ^ 2 * partialX Z (u x y) (v x y) +
          x / radial z x y * partialY Z (u x y) (v x y)) +
        y * (1 / x * partialX Z (u x y) (v x y) +
          y / radial z x y * partialY Z (u x y) (v x y)) =
      (z x y + radial z x y) * transformedDenominator Z z u v x y := by
  rw [hZx, hZy] at hPDE
  apply (div_eq_iff hDen).mp
  calc
    (x * (-y / x ^ 2 * partialX Z (u x y) (v x y) +
          x / radial z x y * partialY Z (u x y) (v x y)) +
        y * (1 / x * partialX Z (u x y) (v x y) +
          y / radial z x y * partialY Z (u x y) (v x y))) /
        transformedDenominator Z z u v x y =
      x * ((-y / x ^ 2 * partialX Z (u x y) (v x y) +
          x / radial z x y * partialY Z (u x y) (v x y)) /
        transformedDenominator Z z u v x y) +
      y * ((1 / x * partialX Z (u x y) (v x y) +
          y / radial z x y * partialY Z (u x y) (v x y)) /
        transformedDenominator Z z u v x y) := by ring
    _ = z x y + radial z x y := hPDE

theorem gap9 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0) (hr : radial z x y ≠ 0)
    (hRadialSq : radial z x y ^ 2 = x ^ 2 + y ^ 2 + z x y ^ 2)
    (hEquation :
      x * (-y / x ^ 2 * partialX Z (u x y) (v x y) +
            x / radial z x y * partialY Z (u x y) (v x y)) +
          y * (1 / x * partialX Z (u x y) (v x y) +
            y / radial z x y * partialY Z (u x y) (v x y)) =
        (z x y + radial z x y) * transformedDenominator Z z u v x y) :
    2 * (z x y + radial z x y) * partialY Z (u x y) (v x y) =
      z x y + radial z x y := by
  have hleft :
      x * (-y / x ^ 2 * partialX Z (u x y) (v x y) +
            x / radial z x y * partialY Z (u x y) (v x y)) +
          y * (1 / x * partialX Z (u x y) (v x y) +
            y / radial z x y * partialY Z (u x y) (v x y)) =
        (x ^ 2 + y ^ 2) / radial z x y *
          partialY Z (u x y) (v x y) := by
    field_simp [hx, hr]
    ring
  rw [hleft] at hEquation
  unfold transformedDenominator at hEquation
  field_simp [hr] at hEquation
  apply mul_left_cancel₀ hr
  linear_combination hEquation +
    partialY Z (u x y) (v x y) * hRadialSq

theorem gap10 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : z x y + radial z x y ≠ 0)
    (hEquation :
      2 * (z x y + radial z x y) * partialY Z (u x y) (v x y) =
        z x y + radial z x y) :
    partialY Z (u x y) (v x y) = (1 : ℝ) / 2 := by
  have htwo : 2 * partialY Z (u x y) (v x y) = 1 := by
    apply mul_left_cancel₀ hSum
    simpa [mul_assoc, mul_left_comm, mul_comm] using hEquation
  nlinarith

theorem gap11 (Z : ℝ → ℝ → ℝ)
    (hZC1 : ContDiff ℝ 1 (Function.uncurry Z))
    (hDerivative : ∀ a b, partialY Z a b = (1 : ℝ) / 2) :
    ∃ φ : ℝ → ℝ, ∀ a b, Z a b = (1 : ℝ) / 2 * b + φ a := by
  refine ⟨fun a => Z a 0, ?_⟩
  intro a b
  have hZDiff : Differentiable ℝ (Function.uncurry Z) :=
    hZC1.differentiable (by norm_num)
  have hline (c : ℝ) :=
    (hasFDerivAt_const (𝕜 := ℝ) a c).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) c)
  have hSlice (c : ℝ) : DifferentiableAt ℝ (fun t : ℝ => Z a t) c := by
    have hOuter : DifferentiableAt ℝ (Function.uncurry Z) (a, c) :=
      hZDiff (a, c)
    simpa [Function.uncurry, id_eq] using
      (hOuter.hasFDerivAt.comp c (hline c)).differentiableAt
  have hgDeriv (c : ℝ) :
      HasDerivAt (fun t : ℝ => Z a t - (1 : ℝ) / 2 * t) 0 c := by
    have hd : deriv (fun t : ℝ => Z a t) c = (1 : ℝ) / 2 := by
      simpa [partialY] using hDerivative a c
    have hZDeriv : HasDerivAt (fun t : ℝ => Z a t) ((1 : ℝ) / 2) c := by
      rw [← hd]
      exact (hSlice c).hasDerivAt
    convert hZDeriv.sub
      ((hasDerivAt_const c ((1 : ℝ) / 2)).mul (hasDerivAt_id c)) using 1 <;>
      ring
  have hconst := is_const_of_deriv_eq_zero
    (fun c => (hgDeriv c).differentiableAt)
    (fun c => (hgDeriv c).deriv) b 0
  simp only [mul_zero, sub_zero] at hconst
  linarith

theorem gap12 (u v z Z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hU : ∀ x y, x ≠ 0 → u x y = y / x)
    (hV : ∀ x y, x ≠ 0 → v x y = z x y + radial z x y)
    (hRepresentation : ∀ a b, Z a b = (1 : ℝ) / 2 * b + φ a) :
    ∀ x y, x ≠ 0 →
      (1 : ℝ) / 2 * v x y + φ (u x y) =
        (1 : ℝ) / 2 * (z x y + radial z x y) + φ (y / x) := by
  intro x y hx
  rw [hV x y hx, hU x y hx]

theorem gap13 (u v z Z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hCompose : ∀ x y, x ≠ 0 → z x y = Z (u x y) (v x y))
    (hRepresentation : ∀ a b, Z a b = (1 : ℝ) / 2 * b + φ a)
    (hSubstituted : ∀ x y, x ≠ 0 →
      (1 : ℝ) / 2 * v x y + φ (u x y) =
        (1 : ℝ) / 2 * (z x y + radial z x y) + φ (y / x)) :
    ∀ x y, x ≠ 0 →
      z x y = (1 : ℝ) / 2 * (z x y + radial z x y) + φ (y / x) := by
  intro x y hx
  calc
    z x y = Z (u x y) (v x y) := hCompose x y hx
    _ = (1 : ℝ) / 2 * v x y + φ (u x y) :=
      hRepresentation (u x y) (v x y)
    _ = (1 : ℝ) / 2 * (z x y + radial z x y) + φ (y / x) :=
      hSubstituted x y hx

theorem gap14 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hRepresentation : ∀ x y, x ≠ 0 →
      z x y = (1 : ℝ) / 2 * (z x y + radial z x y) + φ (y / x)) :
    ∀ x y, x ≠ 0 →
      (1 : ℝ) / 2 * z x y =
        (1 : ℝ) / 2 * radial z x y + φ (y / x) := by
  intro x y hx
  have h := hRepresentation x y hx
  linarith

theorem gap15 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hHalf : ∀ x y, x ≠ 0 →
      (1 : ℝ) / 2 * z x y =
        (1 : ℝ) / 2 * radial z x y + φ (y / x)) :
    ∀ x y, x ≠ 0 →
      z x y - radial z x y = (fun t => 2 * φ t) (y / x) := by
  intro x y hx
  have h := hHalf x y hx
  dsimp
  linarith

end

end ProofGap.Exercise3464
