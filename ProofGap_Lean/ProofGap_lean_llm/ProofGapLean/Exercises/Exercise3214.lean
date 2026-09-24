import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3214

noncomputable section

def u (x y : ℝ) : ℝ :=
  x * y + x / y

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def secondXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def secondYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def mixedXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

theorem gap1 :
    ∀ x y : ℝ, y ≠ 0 →
      partialX u x y = y + 1 / y := by
  intro x y hy
  have h :=
    ((hasDerivAt_id x).mul (hasDerivAt_const x y)).add
      ((hasDerivAt_id x).div (hasDerivAt_const x y) hy)
  convert h.deriv using 1 <;>
    simp only [partialX, u, id_eq, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, sub_zero] <;>
    field_simp [hy] <;>
    ring

theorem gap2 :
    ∀ x y : ℝ, y ≠ 0 →
      partialY u x y = x - x / y ^ 2 := by
  intro x y hy
  have h :=
    ((hasDerivAt_const y x).mul (hasDerivAt_id y)).add
      ((hasDerivAt_const y x).div (hasDerivAt_id y) hy)
  convert h.deriv using 1 <;>
    simp only [partialY, u, id_eq, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, zero_sub] <;>
    field_simp [hy] <;>
    ring

theorem gap3 :
    ∀ x y : ℝ, y ≠ 0 →
      secondXX u x y = 0 := by
  intro x y hy
  unfold secondXX
  have hfun :
      (fun t : ℝ => partialX u t y) =
        (fun _ : ℝ => y + 1 / y) := by
    funext t
    exact gap1 t y hy
  rw [hfun]
  simpa using (hasDerivAt_const x (y + 1 / y)).deriv

theorem gap4 :
    ∀ x y : ℝ, y ≠ 0 →
      secondYY u x y = 2 * x / y ^ 3 := by
  intro x y hy
  unfold secondYY
  have heq :
      (fun t : ℝ => partialY u x t) =ᶠ[nhds y]
        (fun t : ℝ => x - x / t ^ 2) := by
    exact (eventually_ne_nhds hy).mono (by
      intro t ht
      exact gap2 x t ht)
  have hsq :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    convert (hasDerivAt_id y).mul (hasDerivAt_id y) using 1 <;>
      simp [pow_two, id_eq, two_mul]
    funext t
    rfl
  have hraw :
      HasDerivAt (fun t : ℝ => x - x / t ^ 2)
        (0 - ((0 * y ^ 2 - x * (2 * y)) / (y ^ 2) ^ 2)) y :=
    (hasDerivAt_const y x).sub
      ((hasDerivAt_const y x).div hsq (pow_ne_zero 2 hy))
  calc
    deriv (fun t : ℝ => partialY u x t) y =
        deriv (fun t : ℝ => x - x / t ^ 2) y := heq.deriv_eq
    _ = 0 - ((0 * y ^ 2 - x * (2 * y)) / (y ^ 2) ^ 2) := hraw.deriv
    _ = 2 * x / y ^ 3 := by
      field_simp [hy]
      ring

theorem gap5 :
    ∀ x y : ℝ, y ≠ 0 →
      mixedXY u x y = 1 - 1 / y ^ 2 := by
  intro x y hy
  unfold mixedXY
  have heq :
      (fun t : ℝ => partialX u x t) =ᶠ[nhds y]
        (fun t : ℝ => t + 1 / t) := by
    exact (eventually_ne_nhds hy).mono (by
      intro t ht
      exact gap1 x t ht)
  have hraw :=
    (hasDerivAt_id y).add
      ((hasDerivAt_const y 1).div (hasDerivAt_id y) hy)
  have hg :
      HasDerivAt (fun t : ℝ => t + 1 / t)
        (1 - 1 / y ^ 2) y := by
    convert hraw using 1 <;>
      simp [id_eq, div_eq_mul_inv, sub_eq_add_neg]
  calc
    deriv (fun t : ℝ => partialX u x t) y =
        deriv (fun t : ℝ => t + 1 / t) y := heq.deriv_eq
    _ = 1 - 1 / y ^ 2 := hg.deriv

end

end ProofGap.Exercise3214
