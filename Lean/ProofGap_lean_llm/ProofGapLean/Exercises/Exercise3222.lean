import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3222

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.arctan (y / x)

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

private lemma sum_sq_ne_zero_of_left_ne_zero (x y : ℝ) (hx : x ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 :=
  ne_of_gt
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y))

theorem gap1 :
    ∀ x y : ℝ, x ≠ 0 →
      partialX u x y =
        (1 / (1 + (y / x) ^ 2)) * (-(y / x ^ 2)) := by
  intro x y hx
  unfold partialX u
  have hdiv :
      HasDerivAt (fun t : ℝ => y / t) (-(y / x ^ 2)) x := by
    convert (hasDerivAt_const x y).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> ring
  simpa only [Function.comp_apply] using
    ((Real.hasDerivAt_arctan (y / x)).comp x hdiv).deriv

theorem gap2 :
    ∀ y x : ℝ, x ≠ 0 →
      (1 / (1 + (y / x) ^ 2)) * (-(y / x ^ 2)) =
        -(y / (x ^ 2 + y ^ 2)) := by
  intro y x hx
  have hden : x ^ 2 + y ^ 2 ≠ 0 :=
    sum_sq_ne_zero_of_left_ne_zero x y hx
  field_simp [hx, hden] <;> ring

theorem gap3 :
    ∀ x y : ℝ, x ≠ 0 →
      partialX u x y = -(y / (x ^ 2 + y ^ 2)) := by
  intro x y hx
  exact (gap1 x y hx).trans (gap2 y x hx)

theorem gap4 :
    ∀ x y : ℝ, x ≠ 0 →
      partialY u x y =
        (1 / (1 + (y / x) ^ 2)) * (1 / x) := by
  intro x y hx
  unfold partialY u
  have hdiv : HasDerivAt (fun t : ℝ => t / x) (1 / x) y := by
    convert (hasDerivAt_id y).div_const x using 1 <;> ring
  simpa only [Function.comp_apply] using
    ((Real.hasDerivAt_arctan (y / x)).comp y hdiv).deriv

theorem gap5 :
    ∀ y x : ℝ, x ≠ 0 →
      (1 / (1 + (y / x) ^ 2)) * (1 / x) =
        x / (x ^ 2 + y ^ 2) := by
  intro y x hx
  have hden : x ^ 2 + y ^ 2 ≠ 0 :=
    sum_sq_ne_zero_of_left_ne_zero x y hx
  field_simp [hx, hden] <;> ring

theorem gap6 :
    ∀ x y : ℝ, x ≠ 0 →
      partialY u x y = x / (x ^ 2 + y ^ 2) := by
  intro x y hx
  exact (gap4 x y hx).trans (gap5 y x hx)

theorem gap7 :
    ∀ x y : ℝ, x ≠ 0 →
      secondXX u x y =
        2 * x * y / (x ^ 2 + y ^ 2) ^ 2 := by
  intro x y hx
  unfold secondXX
  have hden : x ^ 2 + y ^ 2 ≠ 0 :=
    sum_sq_ne_zero_of_left_ne_zero x y hx
  have hq :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add
      (hasDerivAt_const x (y ^ 2)) using 1 <;>
      simp [id] <;> ring
  have hr :
      HasDerivAt (fun t : ℝ => -(y / (t ^ 2 + y ^ 2)))
        (2 * x * y / (x ^ 2 + y ^ 2) ^ 2) x := by
    convert ((hasDerivAt_const x y).div hq hden).neg using 1 <;>
      field_simp [hden] <;> ring
  have heq :
      Filter.EventuallyEq (nhds x)
        (fun t : ℝ => partialX u t y)
        (fun t : ℝ => -(y / (t ^ 2 + y ^ 2))) :=
    (eventually_ne_nhds hx).mono (fun t ht => gap3 t y ht)
  exact (hr.congr_of_eventuallyEq heq).deriv

theorem gap8 :
    ∀ x y : ℝ, x ≠ 0 →
      secondYY u x y =
        -(2 * x * y / (x ^ 2 + y ^ 2) ^ 2) := by
  intro x y hx
  unfold secondYY
  have heq :
      (fun t : ℝ => partialY u x t) =
        (fun t : ℝ => x / (x ^ 2 + t ^ 2)) := by
    funext t
    exact gap6 x t hx
  rw [heq]
  have hden : x ^ 2 + y ^ 2 ≠ 0 :=
    sum_sq_ne_zero_of_left_ne_zero x y hx
  have hq :
      HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert (hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).pow 2) using 1 <;>
      simp [id] <;> ring
  have hr :
      HasDerivAt (fun t : ℝ => x / (x ^ 2 + t ^ 2))
        (-(2 * x * y / (x ^ 2 + y ^ 2) ^ 2)) y := by
    convert (hasDerivAt_const y x).div hq hden using 1 <;>
      field_simp [hden] <;> ring
  exact hr.deriv

theorem gap9 :
    ∀ x y : ℝ, x ≠ 0 →
      mixedXY u x y =
        -(1 / (x ^ 2 + y ^ 2)) +
          (y * (2 * y)) / (x ^ 2 + y ^ 2) ^ 2 := by
  intro x y hx
  unfold mixedXY
  have heq :
      (fun t : ℝ => partialX u x t) =
        (fun t : ℝ => -(t / (x ^ 2 + t ^ 2))) := by
    funext t
    exact gap3 x t hx
  rw [heq]
  have hden : x ^ 2 + y ^ 2 ≠ 0 :=
    sum_sq_ne_zero_of_left_ne_zero x y hx
  have hq :
      HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert (hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).pow 2) using 1 <;>
      simp [id] <;> ring
  have hr :
      HasDerivAt (fun t : ℝ => -(t / (x ^ 2 + t ^ 2)))
        (-(1 / (x ^ 2 + y ^ 2)) +
          (y * (2 * y)) / (x ^ 2 + y ^ 2) ^ 2) y := by
    convert ((hasDerivAt_id y).div hq hden).neg using 1 <;>
      simp [id] <;> field_simp [hden] <;> ring
  exact hr.deriv

theorem gap10 :
    ∀ x y : ℝ, x ≠ 0 →
      -(1 / (x ^ 2 + y ^ 2)) +
          (y * (2 * y)) / (x ^ 2 + y ^ 2) ^ 2 =
        -((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2) := by
  intro x y hx
  have hden : x ^ 2 + y ^ 2 ≠ 0 :=
    sum_sq_ne_zero_of_left_ne_zero x y hx
  field_simp [hden] <;> ring

theorem gap11 :
    ∀ x y : ℝ, x ≠ 0 →
      mixedXY u x y =
        -((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2) := by
  intro x y hx
  exact (gap9 x y hx).trans (gap10 x y hx)

end

end ProofGap.Exercise3222
