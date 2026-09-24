import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1045

noncomputable section

def xCoord (t : ℝ) : ℝ := Real.exp (2 * t) * Real.cos t ^ 2
def yCoord (t : ℝ) : ℝ := Real.exp (2 * t) * Real.sin t ^ 2
def paramDerivative (t : ℝ) : ℝ := deriv yCoord t / deriv xCoord t

def expanded (t : ℝ) : ℝ :=
  (2 * Real.exp (2 * t) * (Real.sin t ^ 2 + Real.sin t * Real.cos t)) /
    (2 * Real.exp (2 * t) * (Real.cos t ^ 2 - Real.sin t * Real.cos t))

def shifted (t : ℝ) : ℝ :=
  (Real.sin t * Real.sqrt 2 * Real.sin (t + Real.pi / 4)) /
    (Real.cos t * Real.sqrt 2 * Real.cos (t + Real.pi / 4))

private theorem coordDerivatives (t : ℝ) :
    deriv yCoord t =
        2 * Real.exp (2 * t) *
          (Real.sin t ^ 2 + Real.sin t * Real.cos t) ∧
      deriv xCoord t =
        2 * Real.exp (2 * t) *
          (Real.cos t ^ 2 - Real.sin t * Real.cos t) := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (2 * s))
      (2 * Real.exp (2 * t)) t := by
    convert (Real.hasDerivAt_exp (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2) using 1 <;> ring
  have hsinSq : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin t * Real.cos t) t := by
    convert (Real.hasDerivAt_sin t).pow 2 using 1 <;> ring
  have hcosSq : HasDerivAt (fun s : ℝ => Real.cos s ^ 2)
      (-2 * Real.sin t * Real.cos t) t := by
    convert (Real.hasDerivAt_cos t).pow 2 using 1 <;> ring
  have hy : HasDerivAt yCoord
      (2 * Real.exp (2 * t) *
        (Real.sin t ^ 2 + Real.sin t * Real.cos t)) t := by
    convert hexp.mul hsinSq using 1 <;> ring
  have hx : HasDerivAt xCoord
      (2 * Real.exp (2 * t) *
        (Real.cos t ^ 2 - Real.sin t * Real.cos t)) t := by
    convert hexp.mul hcosSq using 1 <;> ring
  exact ⟨hy.deriv, hx.deriv⟩

theorem gap1 (t : ℝ)
    (hden : Real.cos t ^ 2 - Real.sin t * Real.cos t ≠ 0) :
    paramDerivative t = expanded t := by
  rcases coordDerivatives t with ⟨hy, hx⟩
  simp only [paramDerivative, expanded, hy, hx]

theorem gap2 (t : ℝ) (hcos : Real.cos t ≠ 0)
    (hshift : Real.cos (t + Real.pi / 4) ≠ 0) :
    paramDerivative t = shifted t := by
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsin_id :
      Real.sqrt 2 * Real.sin (t + Real.pi / 4) =
        Real.sin t + Real.cos t := by
    rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
    calc
      Real.sqrt 2 *
          (Real.sin t * (Real.sqrt 2 / 2) +
            Real.cos t * (Real.sqrt 2 / 2)) =
          Real.sqrt 2 ^ 2 / 2 * (Real.sin t + Real.cos t) := by ring
      _ = Real.sin t + Real.cos t := by
        rw [hsqrt_sq]
        ring
  have hcos_id :
      Real.sqrt 2 * Real.cos (t + Real.pi / 4) =
        Real.cos t - Real.sin t := by
    rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
    calc
      Real.sqrt 2 *
          (Real.cos t * (Real.sqrt 2 / 2) -
            Real.sin t * (Real.sqrt 2 / 2)) =
          Real.sqrt 2 ^ 2 / 2 * (Real.cos t - Real.sin t) := by ring
      _ = Real.cos t - Real.sin t := by
        rw [hsqrt_sq]
        ring
  have hdiff : Real.cos t - Real.sin t ≠ 0 := by
    rw [← hcos_id]
    exact mul_ne_zero hsqrt_ne hshift
  have hden : Real.cos t ^ 2 - Real.sin t * Real.cos t ≠ 0 := by
    rw [show Real.cos t ^ 2 - Real.sin t * Real.cos t =
      Real.cos t * (Real.cos t - Real.sin t) by ring]
    exact mul_ne_zero hcos hdiff
  have hnum_shift :
      Real.sin t * Real.sqrt 2 * Real.sin (t + Real.pi / 4) =
        Real.sin t * (Real.sin t + Real.cos t) := by
    calc
      Real.sin t * Real.sqrt 2 * Real.sin (t + Real.pi / 4) =
          Real.sin t * (Real.sqrt 2 * Real.sin (t + Real.pi / 4)) := by ring
      _ = Real.sin t * (Real.sin t + Real.cos t) := by rw [hsin_id]
  have hden_shift :
      Real.cos t * Real.sqrt 2 * Real.cos (t + Real.pi / 4) =
        Real.cos t * (Real.cos t - Real.sin t) := by
    calc
      Real.cos t * Real.sqrt 2 * Real.cos (t + Real.pi / 4) =
          Real.cos t * (Real.sqrt 2 * Real.cos (t + Real.pi / 4)) := by ring
      _ = Real.cos t * (Real.cos t - Real.sin t) := by rw [hcos_id]
  rw [gap1 t hden]
  unfold expanded shifted
  rw [hnum_shift, hden_shift]
  field_simp [Real.exp_ne_zero, hcos, hdiff, hden] <;> ring

theorem gap3 (t : ℝ) (hcos : Real.cos t ≠ 0)
    (hshift : Real.cos (t + Real.pi / 4) ≠ 0) :
    paramDerivative t = Real.tan t * Real.tan (t + Real.pi / 4) := by
  rw [gap2 t hcos hshift]
  unfold shifted
  simp only [Real.tan_eq_sin_div_cos]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hcos, hshift, hsqrt_ne] <;> ring

end

end ProofGap.Exercise1045
