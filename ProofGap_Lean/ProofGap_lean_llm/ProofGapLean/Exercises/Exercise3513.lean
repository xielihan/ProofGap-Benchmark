import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3513

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def coordU (x y : ℝ) : ℝ := x / y

def coordV (x y : ℝ) : ℝ := x

def transformedValue (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * z x y - y

def physicalPDE (z : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  y * partialYY z x y + 2 * partialY z x y = 2 / x

private theorem hasDerivAt_partialY
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t : ℝ => f x t) (partialY f x y) y := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by fun_prop
  have hc : DifferentiableAt ℝ (fun t : ℝ => f x t) y := by
    simpa [Function.uncurry, Function.comp_def] using hf.comp y hp
  simpa [partialY] using hc.hasDerivAt

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) {x dg dh : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (g x, h x))
    (hg : HasDerivAt g dg x) (hh : HasDerivAt h dh x) :
    HasDerivAt (fun t => F (g t) (h t))
      (dg * partialX F (g x) (h x) + dh * partialY F (g x) (h x)) x := by
  let D := fderiv ℝ (Function.uncurry F) (g x, h x)
  have hc := hF.hasFDerivAt.comp x
    (hg.hasFDerivAt.prodMk hh.hasFDerivAt)
  have hc' : HasDerivAt (fun t => F (g t) (h t)) (D (dg, dh)) x := by
    simpa [D, Function.comp_def, Function.uncurry] using hc.hasDerivAt
  have hdx0 : HasDerivAt (fun t : ℝ => F t (h x))
      (D (1, 0)) (g x) := by
    have hx := hF.hasFDerivAt.comp (g x)
      ((hasDerivAt_id (g x)).hasFDerivAt.prodMk
        (hasDerivAt_const (g x) (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hx.hasDerivAt
  have hdx : partialX F (g x) (h x) = D (1, 0) := by
    change deriv (fun t : ℝ => F t (h x)) (g x) = D (1, 0)
    exact hdx0.deriv
  have hdy0 : HasDerivAt (fun t : ℝ => F (g x) t)
      (D (0, 1)) (h x) := by
    have hy := hF.hasFDerivAt.comp (h x)
      ((hasDerivAt_const (h x) (g x)).hasFDerivAt.prodMk
        (hasDerivAt_id (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hy.hasDerivAt
  have hdy : partialY F (g x) (h x) = D (0, 1) := by
    change deriv (fun t : ℝ => F (g x) t) (h x) = D (0, 1)
    exact hdy0.deriv
  have hlin : D (dg, dh) = dg * D (1, 0) + dh * D (0, 1) := by
    calc
      D (dg, dh) = D (dg • (1, 0) + dh • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = dg • D (1, 0) + dh • D (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = dg * D (1, 0) + dh * D (0, 1) := by simp
  convert hc' using 1
  simpa [hdx, hdy] using hlin.symm

private theorem hasDerivAt_coordU (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => coordU x t) (-(x / y ^ 2)) y := by
  unfold coordU
  convert (hasDerivAt_const y x).div (hasDerivAt_id y) hy using 1 <;>
    simp only [id_eq] <;> field_simp [hy] <;> ring

private theorem hasDerivAt_coordV (x y : ℝ) :
    HasDerivAt (fun t : ℝ => coordV x t) 0 y := by
  unfold coordV
  exact hasDerivAt_const y x

theorem gap1 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y, y ≠ 0 →
      W (coordU x y) (coordV x y) = transformedValue z x y) :
    ∀ x y, y ≠ 0 →
      partialY (fun a b => W (coordU a b) (coordV a b)) x y =
        x * partialY z x y - 1 := by
  intro x y hy
  have hloc : (fun t : ℝ => W (coordU x t) (coordV x t)) =ᶠ[nhds y]
      (fun t : ℝ => x * z x t - t) := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    simpa [transformedValue] using hRelation x t ht
  have hz' := hasDerivAt_partialY z x y (hz.1 (x, y))
  have hR := hz'.const_mul x |>.sub (hasDerivAt_id y)
  unfold partialY
  exact hloc.deriv_eq.trans (by simpa using hR.deriv)

-- Statement correction: the chain rule for `coordU x y = x / y`
-- requires `y ≠ 0`; the original universal statement is false at `y = 0`.
theorem gap2 (W : ℝ → ℝ → ℝ)
    (hW : C2 W) :
    ∀ x y, y ≠ 0 →
      partialY (fun a b => W (coordU a b) (coordV a b)) x y =
        partialX W (coordU x y) (coordV x y) * partialY coordU x y +
          partialY W (coordU x y) (coordV x y) * partialY coordV x y := by
  intro x y hy
  have hu := hasDerivAt_coordU x y hy
  have hv := hasDerivAt_coordV x y
  have hcomp := hasDerivAt_comp₂ W (fun t => coordU x t) (fun t => coordV x t)
    (hW.1 (coordU x y, coordV x y)) hu hv
  have hdu : partialY coordU x y = -(x / y ^ 2) := by
    exact hu.deriv
  have hdv : partialY coordV x y = 0 := by
    exact hv.deriv
  rw [hdu, hdv]
  change deriv (fun t => W (coordU x t) (coordV x t)) y = _
  rw [hcomp.deriv]
  ring

theorem gap3 (W : ℝ → ℝ → ℝ) :
    ∀ x y, y ≠ 0 →
      partialX W (coordU x y) (coordV x y) * partialY coordU x y +
          partialY W (coordU x y) (coordV x y) * partialY coordV x y =
        -x / y ^ 2 * partialX W (coordU x y) (coordV x y) := by
  intro x y hy
  have hdu : partialY coordU x y = -(x / y ^ 2) :=
    (hasDerivAt_coordU x y hy).deriv
  have hdv : partialY coordV x y = 0 :=
    (hasDerivAt_coordV x y).deriv
  rw [hdu, hdv]
  ring

theorem gap4 (W : ℝ → ℝ → ℝ)
    (hW : C2 W) :
    ∀ x y, y ≠ 0 →
      partialY (fun a b => W (coordU a b) (coordV a b)) x y =
        -x / y ^ 2 * partialX W (coordU x y) (coordV x y) := by
  intro x y hy
  exact (gap2 W hW x y hy).trans (gap3 W x y hy)

theorem gap5 (z W : ℝ → ℝ → ℝ)
    (hW : C2 W)
    (hRelation : ∀ x y, y ≠ 0 →
      W (coordU x y) (coordV x y) = transformedValue z x y) :
    ∀ x y, x ≠ 0 → y ≠ 0 →
      partialY z x y =
        1 / x - 1 / y ^ 2 * partialX W (coordU x y) (coordV x y) := by
  intro x y hx hy
  have hloc : (fun t : ℝ => z x t) =ᶠ[nhds y]
      (fun t : ℝ => (W (coordU x t) (coordV x t) + t) / x) := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    have hrel := hRelation x t ht
    unfold transformedValue at hrel
    field_simp [hx] at hrel ⊢
    linarith
  have hu := hasDerivAt_coordU x y hy
  have hv := hasDerivAt_coordV x y
  have hcomp := hasDerivAt_comp₂ W (fun t => coordU x t) (fun t => coordV x t)
    (hW.1 (coordU x y, coordV x y)) hu hv
  have hR := (hcomp.add (hasDerivAt_id y)).div_const x
  have hR' : HasDerivAt
      (fun t : ℝ => (W (coordU x t) (coordV x t) + t) / x)
      ((-(x / y ^ 2) * partialX W (coordU x y) (coordV x y) +
          0 * partialY W (coordU x y) (coordV x y) + 1) / x) y := by
    simpa only [Pi.add_apply, id_eq] using hR
  unfold partialY
  rw [hloc.deriv_eq, hR'.deriv]
  field_simp [hx, hy]
  ring

theorem gap6 (z : ℝ → ℝ → ℝ) :
    ∀ x y, y ≠ 0 →
      y * partialYY z x y + 2 * partialY z x y =
        1 / y * (y ^ 2 * partialYY z x y + 2 * y * partialY z x y) := by
  intro x y hy
  field_simp [hy]

theorem gap7 (z W : ℝ → ℝ → ℝ)
    (hW : C2 W)
    (hRelation : ∀ x y, y ≠ 0 →
      W (coordU x y) (coordV x y) = transformedValue z x y) :
    ∀ x y, x ≠ 0 → y ≠ 0 →
      y * partialYY z x y + 2 * partialY z x y =
        2 / x + x / y ^ 3 * partialXX W (coordU x y) (coordV x y) := by
  intro x y hx hy
  have hzy : (fun t : ℝ => partialY z x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        1 / x - 1 / t ^ 2 * partialX W (coordU x t) (coordV x t)) := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    exact gap5 z W hW hRelation x t hx ht
  have hu := hasDerivAt_coordU x y hy
  have hv := hasDerivAt_coordV x y
  have hB := hasDerivAt_comp₂ (partialX W)
    (fun t => coordU x t) (fun t => coordV x t)
    (hW.2.1 (coordU x y, coordV x y)) hu hv
  have hsq : HasDerivAt (fun t : ℝ => 1 / t ^ 2) (-(2 / y ^ 3)) y := by
    have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
      convert (hasDerivAt_id y).pow 2 using 1 <;> norm_num <;> ring
    have hq : HasDerivAt (fun t : ℝ => 1 / t ^ 2)
        ((0 * y ^ 2 - 1 * (2 * y)) / (y ^ 2) ^ 2) y :=
      (hasDerivAt_const y 1).div hp (pow_ne_zero 2 hy)
    convert hq using 1 <;> field_simp [hy] <;> ring
  have hR := (hasDerivAt_const y (1 / x)).sub (hsq.mul hB)
  have hR' : HasDerivAt
      (fun t : ℝ =>
        1 / x - 1 / t ^ 2 * partialX W (coordU x t) (coordV x t))
      (0 - (-(2 / y ^ 3) * partialX W (coordU x y) (coordV x y) +
        1 / y ^ 2 *
          (-(x / y ^ 2) * partialX (partialX W)
              (coordU x y) (coordV x y) +
            0 * partialY (partialX W) (coordU x y) (coordV x y)))) y := by
    simpa only [Pi.sub_apply, Pi.mul_apply, id_eq] using hR
  have hxxW : partialX (partialX W) (coordU x y) (coordV x y) =
      partialXX W (coordU x y) (coordV x y) := by
    rfl
  rw [hxxW] at hR'
  have hyy : partialYY z x y =
      2 / y ^ 3 * partialX W (coordU x y) (coordV x y) +
        x / y ^ 4 * partialXX W (coordU x y) (coordV x y) := by
    change deriv (fun t : ℝ => partialY z x t) y = _
    rw [hzy.deriv_eq, hR'.deriv]
    field_simp [hy]
    ring
  rw [hyy, gap5 z W hW hRelation x y hx hy]
  field_simp [hx, hy]
  ring

theorem gap8 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ a b, b ≠ 0 →
      W (coordU a b) (coordV a b) = transformedValue z a b)
    (hPDE : physicalPDE z x y) :
    partialXX W (coordU x y) (coordV x y) = 0 := by
  have h7 := gap7 z W hW hRelation x y hx hy
  unfold physicalPDE at hPDE
  have hp :
      x / y ^ 3 * partialXX W (coordU x y) (coordV x y) = 0 := by
    linarith
  exact (mul_eq_zero.mp hp).resolve_left
    (div_ne_zero hx (pow_ne_zero 3 hy))

end

end ProofGap.Exercise3513
