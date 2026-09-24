import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3258

noncomputable section

def u (x y : ℝ) : ℝ :=
  x ^ 3 * Real.sin y + y ^ 3 * Real.sin x

def partialXOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g t y) x

def mixedX3Y3 (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[3]) (fun t => partialXOrder 3 g x t) y

private theorem sin_shift_three_pi_div_two (x : ℝ) :
    Real.sin (x + 3 * Real.pi / 2) = -Real.cos x := by
  have h : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by
    ring
  rw [h, Real.sin_add, Real.sin_add, Real.cos_add]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two,
    Real.cos_pi_div_two] <;> ring

theorem gap1 :
    ∀ x y, partialXOrder 3 u x y =
      6 * Real.sin y + y ^ 3 * Real.sin (x + 3 * Real.pi / 2) := by
  intro x y
  have h1 :
      deriv (fun t : ℝ => u t y) =
        fun t => 3 * t ^ 2 * Real.sin y + y ^ 3 * Real.cos t := by
    funext t
    have ht : HasDerivAt (fun t : ℝ => u t y)
        (3 * t ^ 2 * Real.sin y + y ^ 3 * Real.cos t) t := by
      unfold u
      convert
        ((((hasDerivAt_id t).pow 3).mul_const (Real.sin y)).add
          ((Real.hasDerivAt_sin t).const_mul (y ^ 3))) using 1 <;>
        simp only [id_eq] <;> ring
    exact ht.deriv
  have h2 :
      deriv (fun t : ℝ => 3 * t ^ 2 * Real.sin y + y ^ 3 * Real.cos t) =
        fun t => 6 * t * Real.sin y - y ^ 3 * Real.sin t := by
    funext t
    have ht : HasDerivAt
        (fun t : ℝ => 3 * t ^ 2 * Real.sin y + y ^ 3 * Real.cos t)
        (6 * t * Real.sin y - y ^ 3 * Real.sin t) t := by
      convert
        (((((hasDerivAt_id t).pow 2).const_mul 3).mul_const (Real.sin y)).add
          ((Real.hasDerivAt_cos t).const_mul (y ^ 3))) using 1 <;>
        simp only [id_eq] <;> ring
    exact ht.deriv
  have h3 :
      deriv (fun t : ℝ => 6 * t * Real.sin y - y ^ 3 * Real.sin t) =
        fun t => 6 * Real.sin y - y ^ 3 * Real.cos t := by
    funext t
    have ht : HasDerivAt
        (fun t : ℝ => 6 * t * Real.sin y - y ^ 3 * Real.sin t)
        (6 * Real.sin y - y ^ 3 * Real.cos t) t := by
      convert
        ((((hasDerivAt_id t).const_mul 6).mul_const (Real.sin y)).sub
          ((Real.hasDerivAt_sin t).const_mul (y ^ 3))) using 1 <;> ring
    exact ht.deriv
  unfold partialXOrder
  change deriv (deriv (deriv (fun t : ℝ => u t y))) x = _
  rw [h1, h2, h3, sin_shift_three_pi_div_two]
  ring

theorem gap2 :
    ∀ y x,
      6 * Real.sin y + y ^ 3 * Real.sin (x + 3 * Real.pi / 2) =
        6 * Real.sin y - y ^ 3 * Real.cos x := by
  intro y x
  rw [sin_shift_three_pi_div_two] <;> ring

theorem gap3 :
    ∀ x y, partialXOrder 3 u x y =
      6 * Real.sin y - y ^ 3 * Real.cos x := by
  intro x y
  exact (gap1 x y).trans (gap2 y x)

theorem gap4 :
    ∀ x y, mixedX3Y3 u x y =
      6 * Real.sin (y + 3 * Real.pi / 2) - 6 * Real.cos x := by
  intro x y
  have h0 :
      (fun t : ℝ => partialXOrder 3 u x t) =
        fun t => 6 * Real.sin t - t ^ 3 * Real.cos x := by
    funext t
    exact gap3 x t
  have h1 :
      deriv (fun t : ℝ => 6 * Real.sin t - t ^ 3 * Real.cos x) =
        fun t => 6 * Real.cos t - 3 * t ^ 2 * Real.cos x := by
    funext t
    have ht : HasDerivAt
        (fun t : ℝ => 6 * Real.sin t - t ^ 3 * Real.cos x)
        (6 * Real.cos t - 3 * t ^ 2 * Real.cos x) t := by
      convert
        (((Real.hasDerivAt_sin t).const_mul 6).sub
          (((hasDerivAt_id t).pow 3).mul_const (Real.cos x))) using 1 <;>
        simp only [id_eq] <;> ring
    exact ht.deriv
  have h2 :
      deriv (fun t : ℝ => 6 * Real.cos t - 3 * t ^ 2 * Real.cos x) =
        fun t => -6 * Real.sin t - 6 * t * Real.cos x := by
    funext t
    have ht : HasDerivAt
        (fun t : ℝ => 6 * Real.cos t - 3 * t ^ 2 * Real.cos x)
        (-6 * Real.sin t - 6 * t * Real.cos x) t := by
      convert
        (((Real.hasDerivAt_cos t).const_mul 6).sub
          (((((hasDerivAt_id t).pow 2).const_mul 3).mul_const
            (Real.cos x)))) using 1 <;>
        simp only [id_eq] <;> ring
    exact ht.deriv
  have h3 :
      deriv (fun t : ℝ => -6 * Real.sin t - 6 * t * Real.cos x) =
        fun t => -6 * Real.cos t - 6 * Real.cos x := by
    funext t
    have ht : HasDerivAt
        (fun t : ℝ => -6 * Real.sin t - 6 * t * Real.cos x)
        (-6 * Real.cos t - 6 * Real.cos x) t := by
      convert
        (((Real.hasDerivAt_sin t).const_mul (-6)).sub
          (((hasDerivAt_id t).const_mul 6).mul_const (Real.cos x))) using 1 <;>
        ring
    exact ht.deriv
  unfold mixedX3Y3
  change deriv (deriv (deriv (fun t : ℝ => partialXOrder 3 u x t))) y = _
  rw [h0, h1, h2, h3, sin_shift_three_pi_div_two]
  ring

theorem gap5 :
    ∀ y x,
      6 * Real.sin (y + 3 * Real.pi / 2) - 6 * Real.cos x =
        -6 * (Real.cos y + Real.cos x) := by
  intro y x
  rw [sin_shift_three_pi_div_two] <;> ring

theorem gap6 :
    ∀ x y, mixedX3Y3 u x y =
      -6 * (Real.cos y + Real.cos x) := by
  intro x y
  exact (gap4 x y).trans (gap5 y x)

end

end ProofGap.Exercise3258
