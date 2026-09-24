import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise3333

noncomputable section

def radius (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2)

def z (φ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  φ (radius x y)

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

private theorem hasDerivAt_radius_left (x y : ℝ)
    (hxy : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun s : ℝ => radius s y) (x / radius x y) x := by
  have hq_nonneg : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hq_pos : 0 < x ^ 2 + y ^ 2 :=
    lt_of_le_of_ne hq_nonneg (Ne.symm hxy)
  have hsqrt : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq_pos)
  have hpoly :
      HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (((hasDerivAt_id x).pow 2).add_const (y ^ 2))
  have hcomp := (Real.hasDerivAt_sqrt hxy).comp x hpoly
  convert hcomp using 1 <;>
    simp only [radius, Function.comp_apply] <;>
    field_simp [hsqrt] <;>
    ring

theorem gap1 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, x ^ 2 + y ^ 2 ≠ 0 →
      partialX (z φ) x y =
        x * deriv φ (radius x y) / radius x y := by
  intro x y hxy
  unfold partialX z
  have hr := hasDerivAt_radius_left x y hxy
  have hcomp := (hφ (radius x y)).hasDerivAt.comp x hr
  convert hcomp.deriv using 1 <;> ring

theorem gap2 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ x y, x ^ 2 + y ^ 2 ≠ 0 →
      partialY (z φ) x y =
        y * deriv φ (radius x y) / radius x y := by
  intro x y hxy
  unfold partialY z
  have hswap : y ^ 2 + x ^ 2 ≠ 0 := by
    simpa [add_comm] using hxy
  have hr :
      HasDerivAt (fun s : ℝ => radius x s) (y / radius x y) y := by
    simpa [radius, add_comm] using hasDerivAt_radius_left y x hswap
  have hcomp := (hφ (radius x y)).hasDerivAt.comp y hr
  convert hcomp.deriv using 1 <;> ring

theorem gap3 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ y x, x ^ 2 + y ^ 2 ≠ 0 →
      y * partialX (z φ) x y - x * partialY (z φ) x y = 0 := by
  intro y x hxy
  rw [gap1 φ hφ x y hxy, gap2 φ hφ x y hxy]
  ring

theorem gap4 (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) :
    ∀ y x, x ^ 2 + y ^ 2 ≠ 0 →
      y * partialX (z φ) x y - x * partialY (z φ) x y = 0 := by
  exact gap3 φ hφ

end

end ProofGap.Exercise3333
