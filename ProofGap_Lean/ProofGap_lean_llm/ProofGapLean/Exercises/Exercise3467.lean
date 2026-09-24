import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace ProofGap.Exercise3467

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def xiForm (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  y + z x y * Real.exp (-x)

def etaForm (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x + z x y * Real.exp (-y)

def denominator (Z ξ η : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  1 - Real.exp (-x) * partialX Z (ξ x y) (η x y) -
    Real.exp (-y) * partialY Z (ξ x y) (η x y)

private theorem hasFDerivAt_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun p => (f p, g p)) (f'.prod g') x :=
  hf.prodMk hg

private theorem differential_eq_fderiv_apply
    (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    differential f x y dx dy =
      fderiv ℝ (Function.uncurry f) (x, y) (dx, dy) := by
  have hxPair :
      HasFDerivAt (fun t : ℝ => (t, y))
        ((ContinuousLinearMap.id ℝ ℝ).prod
          (0 : ℝ →L[ℝ] ℝ)) x := by
    simpa only [id_eq] using
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk
        (hasFDerivAt_const (𝕜 := ℝ) (x := x) (c := y)))
  have hyPair :
      HasFDerivAt (fun t : ℝ => (x, t))
        ((0 : ℝ →L[ℝ] ℝ).prod
          (ContinuousLinearMap.id ℝ ℝ)) y := by
    simpa only [id_eq] using
      ((hasFDerivAt_const (𝕜 := ℝ) (x := y) (c := x)).prodMk
        (hasFDerivAt_id (𝕜 := ℝ) y))
  have hxComp :
      HasFDerivAt
        (Function.uncurry f ∘ fun t : ℝ => (t, y))
        ((fderiv ℝ (Function.uncurry f) (x, y)).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod
            (0 : ℝ →L[ℝ] ℝ))) x :=
    hf.hasFDerivAt.comp x hxPair
  have hyComp :
      HasFDerivAt
        (Function.uncurry f ∘ fun t : ℝ => (x, t))
        ((fderiv ℝ (Function.uncurry f) (x, y)).comp
          ((0 : ℝ →L[ℝ] ℝ).prod
            (ContinuousLinearMap.id ℝ ℝ))) y :=
    hf.hasFDerivAt.comp y hyPair
  have hxDeriv :
      deriv (fun t : ℝ => f t y) x =
        fderiv ℝ (Function.uncurry f) (x, y) (1, 0) := by
    unfold deriv
    change
      (fderiv ℝ (Function.uncurry f ∘ fun t : ℝ => (t, y)) x) 1 = _
    rw [hxComp.fderiv]
    simp [Function.comp_def]
  have hyDeriv :
      deriv (fun t : ℝ => f x t) y =
        fderiv ℝ (Function.uncurry f) (x, y) (0, 1) := by
    unfold deriv
    change
      (fderiv ℝ (Function.uncurry f ∘ fun t : ℝ => (x, t)) y) 1 = _
    rw [hyComp.fderiv]
    simp [Function.comp_def]
  unfold differential partialX partialY
  rw [hxDeriv, hyDeriv]
  have hcoords :
      (dx, dy) = dx • (1, 0) + dy • (0, 1) := by
    ext <;> simp
  rw [hcoords, map_add, map_smul, map_smul]
  simp [smul_eq_mul, mul_comm]

private theorem implicit_fraction_identity
    (u X Y a b A B D C : ℝ)
    (hD : D ≠ 0)
    (hDdef : D = 1 - a * A - b * B)
    (hC : C = X * Y)
    (hXa : X * a = 1)
    (hYb : Y * b = 1) :
    (u + X) * ((B - u * a * A) / D) +
          (u + Y) * ((A - u * b * B) / D) -
          (u ^ 2 - C) =
      (C - u ^ 2) / D := by
  apply (eq_div_iff hD).2
  have hfirst :
      ((u + X) * ((B - u * a * A) / D)) * D =
        (u + X) * (B - u * a * A) := by
    calc
      ((u + X) * ((B - u * a * A) / D)) * D =
          (u + X) * (((B - u * a * A) / D) * D) := by ring
      _ = (u + X) * (B - u * a * A) := by
        field_simp [hD] <;> ring
  have hsecond :
      ((u + Y) * ((A - u * b * B) / D)) * D =
        (u + Y) * (A - u * b * B) := by
    calc
      ((u + Y) * ((A - u * b * B) / D)) * D =
          (u + Y) * (((A - u * b * B) / D) * D) := by ring
      _ = (u + Y) * (A - u * b * B) := by
        field_simp [hD] <;> ring
  calc
    ((u + X) * ((B - u * a * A) / D) +
          (u + Y) * ((A - u * b * B) / D) -
          (u ^ 2 - C)) * D =
      ((u + X) * ((B - u * a * A) / D)) * D +
          ((u + Y) * ((A - u * b * B) / D)) * D -
          (u ^ 2 - C) * D := by ring
    _ = (u + X) * (B - u * a * A) +
          (u + Y) * (A - u * b * B) -
          (u ^ 2 - C) * D := by
      rw [hfirst, hsecond]
    _ = C - u ^ 2 := by
      rw [hDdef, hC]
      calc
        (u + X) * (B - u * a * A) +
              (u + Y) * (A - u * b * B) -
              (u ^ 2 - X * Y) * (1 - a * A - b * B) =
            X * Y - u ^ 2 +
              A * (u + Y) * (1 - X * a) +
              B * (u + X) * (1 - Y * b) := by ring
        _ = X * Y - u ^ 2 := by simp [hXa, hYb]

theorem gap1 (ξ η z Z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hξDiff : DifferentiableAt ℝ (Function.uncurry ξ) (x, y))
    (hηDiff : DifferentiableAt ℝ (Function.uncurry η) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hZDiff : DifferentiableAt ℝ (Function.uncurry Z) (ξ x y, η x y))
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = Z (ξ p.1 p.2) (η p.1 p.2)) :
    differential z x y dx dy =
      partialX Z (ξ x y) (η x y) * differential ξ x y dx dy +
        partialY Z (ξ x y) (η x y) * differential η x y dx dy := by
  change differential z x y dx dy =
    differential Z (ξ x y) (η x y)
      (differential ξ x y dx dy) (differential η x y dx dy)
  have hComp :
      HasFDerivAt
        (Function.uncurry Z ∘ fun p : ℝ × ℝ =>
          (Function.uncurry ξ p, Function.uncurry η p))
        ((fderiv ℝ (Function.uncurry Z) (ξ x y, η x y)).comp
          ((fderiv ℝ (Function.uncurry ξ) (x, y)).prod
            (fderiv ℝ (Function.uncurry η) (x, y))))
        (x, y) :=
    hZDiff.hasFDerivAt.comp (x, y)
      (hasFDerivAt_pair hξDiff.hasFDerivAt hηDiff.hasFDerivAt)
  have hzChain :
      HasFDerivAt (Function.uncurry z)
        ((fderiv ℝ (Function.uncurry Z) (ξ x y, η x y)).comp
          ((fderiv ℝ (Function.uncurry ξ) (x, y)).prod
            (fderiv ℝ (Function.uncurry η) (x, y))))
        (x, y) := by
    apply hComp.congr_of_eventuallyEq
    simpa [Function.comp_def] using hCompose
  have hDeriv := hzDiff.hasFDerivAt.unique hzChain
  rw [differential_eq_fderiv_apply z x y dx dy hzDiff,
    differential_eq_fderiv_apply ξ x y dx dy hξDiff,
    differential_eq_fderiv_apply η x y dx dy hηDiff,
    differential_eq_fderiv_apply Z (ξ x y) (η x y)
      (fderiv ℝ (Function.uncurry ξ) (x, y) (dx, dy))
      (fderiv ℝ (Function.uncurry η) (x, y) (dx, dy)) hZDiff]
  simpa using congrArg
    (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (dx, dy)) hDeriv

theorem gap2 (ξ η z Z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hξ : ξ x y = xiForm z x y)
    (hη : η x y = etaForm z x y)
    (hDξ : differential ξ x y dx dy =
      dy + Real.exp (-x) * differential z x y dx dy -
        z x y * Real.exp (-x) * dx)
    (hDη : differential η x y dx dy =
      dx + Real.exp (-y) * differential z x y dx dy -
        z x y * Real.exp (-y) * dy) :
    partialX Z (ξ x y) (η x y) * differential ξ x y dx dy +
        partialY Z (ξ x y) (η x y) * differential η x y dx dy =
      partialX Z (ξ x y) (η x y) *
          (dy + Real.exp (-x) * differential z x y dx dy -
            z x y * Real.exp (-x) * dx) +
        partialY Z (ξ x y) (η x y) *
          (dx + Real.exp (-y) * differential z x y dx dy -
            z x y * Real.exp (-y) * dy) := by
  rw [hDξ, hDη]

theorem gap3 (ξ η z Z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hChain :
      differential z x y dx dy =
        partialX Z (ξ x y) (η x y) * differential ξ x y dx dy +
          partialY Z (ξ x y) (η x y) * differential η x y dx dy)
    (hExpand :
      partialX Z (ξ x y) (η x y) * differential ξ x y dx dy +
          partialY Z (ξ x y) (η x y) * differential η x y dx dy =
        partialX Z (ξ x y) (η x y) *
            (dy + Real.exp (-x) * differential z x y dx dy -
              z x y * Real.exp (-x) * dx) +
          partialY Z (ξ x y) (η x y) *
            (dx + Real.exp (-y) * differential z x y dx dy -
              z x y * Real.exp (-y) * dy)) :
    differential z x y dx dy =
      partialX Z (ξ x y) (η x y) *
          (dy + Real.exp (-x) * differential z x y dx dy -
            z x y * Real.exp (-x) * dx) +
        partialY Z (ξ x y) (η x y) *
          (dx + Real.exp (-y) * differential z x y dx dy -
            z x y * Real.exp (-y) * dy) := by
  exact hChain.trans hExpand

theorem gap4 (ξ η z Z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hExpanded :
      differential z x y dx dy =
        partialX Z (ξ x y) (η x y) *
            (dy + Real.exp (-x) * differential z x y dx dy -
              z x y * Real.exp (-x) * dx) +
          partialY Z (ξ x y) (η x y) *
            (dx + Real.exp (-y) * differential z x y dx dy -
              z x y * Real.exp (-y) * dy)) :
    denominator Z ξ η x y * differential z x y dx dy =
      (partialY Z (ξ x y) (η x y) -
          z x y * Real.exp (-x) * partialX Z (ξ x y) (η x y)) * dx +
        (partialX Z (ξ x y) (η x y) -
          z x y * Real.exp (-y) * partialY Z (ξ x y) (η x y)) * dy := by
  unfold denominator
  linear_combination hExpanded

theorem gap5 (ξ η z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : denominator Z ξ η x y ≠ 0)
    (hForm : ∀ dx dy,
      denominator Z ξ η x y * differential z x y dx dy =
        (partialY Z (ξ x y) (η x y) -
            z x y * Real.exp (-x) * partialX Z (ξ x y) (η x y)) * dx +
          (partialX Z (ξ x y) (η x y) -
            z x y * Real.exp (-y) * partialY Z (ξ x y) (η x y)) * dy) :
    partialX z x y =
      (partialY Z (ξ x y) (η x y) -
          z x y * Real.exp (-x) * partialX Z (ξ x y) (η x y)) /
        denominator Z ξ η x y := by
  apply (eq_div_iff hDen).2
  simpa [differential, mul_comm] using hForm 1 0

theorem gap6 (ξ η z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : denominator Z ξ η x y ≠ 0)
    (hForm : ∀ dx dy,
      denominator Z ξ η x y * differential z x y dx dy =
        (partialY Z (ξ x y) (η x y) -
            z x y * Real.exp (-x) * partialX Z (ξ x y) (η x y)) * dx +
          (partialX Z (ξ x y) (η x y) -
            z x y * Real.exp (-y) * partialY Z (ξ x y) (η x y)) * dy) :
    partialY z x y =
      (partialX Z (ξ x y) (η x y) -
          z x y * Real.exp (-y) * partialY Z (ξ x y) (η x y)) /
        denominator Z ξ η x y := by
  apply (eq_div_iff hDen).2
  simpa [differential, mul_comm] using hForm 0 1

theorem gap7 (ξ η z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDen : denominator Z ξ η x y ≠ 0)
    (hZx : partialX z x y =
      (partialY Z (ξ x y) (η x y) -
          z x y * Real.exp (-x) * partialX Z (ξ x y) (η x y)) /
        denominator Z ξ η x y)
    (hZy : partialY z x y =
      (partialX Z (ξ x y) (η x y) -
          z x y * Real.exp (-y) * partialY Z (ξ x y) (η x y)) /
        denominator Z ξ η x y) :
    (z x y + Real.exp x) * partialX z x y +
          (z x y + Real.exp y) * partialY z x y -
          (z x y ^ 2 - Real.exp (x + y)) =
      (Real.exp (x + y) - z x y ^ 2) / denominator Z ξ η x y := by
  rw [hZx, hZy]
  refine implicit_fraction_identity
    (u := z x y) (X := Real.exp x) (Y := Real.exp y)
    (a := Real.exp (-x)) (b := Real.exp (-y))
    (A := partialX Z (ξ x y) (η x y))
    (B := partialY Z (ξ x y) (η x y))
    (D := denominator Z ξ η x y) (C := Real.exp (x + y))
    (hD := hDen) (hDdef := ?_) (hC := ?_) (hXa := ?_) (hYb := ?_)
  · rfl
  · exact Real.exp_add x y
  · calc
      Real.exp x * Real.exp (-x) =
          Real.exp (x + -x) := by
        rw [Real.exp_add]
      _ = 1 := by simp
  · calc
      Real.exp y * Real.exp (-y) =
          Real.exp (y + -y) := by
        rw [Real.exp_add]
      _ = 1 := by simp

end

end ProofGap.Exercise3467
